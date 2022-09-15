import sark
import idaapi
import pefile
import sys
import struct
from typing import Dict, Tuple, List, Set, Optional
from dataclasses import dataclass, field
from enum import Enum, auto

# for debugging:
#import wingdbstub
#wingdbstub.Ensure()


""" 
  ConfuserEx code unflattener in IDA Python
  (c) GovCERT.ch, August 2022
  v1.0 : Aug 26, 2022 - initial version
"""


# Some helper functions to deal with branch functions:
# 0x2b - 0x37 are near (.s) variants, 0x38 - 0x44 far variants (difference with same condition is always 13)
# 0x38 / 0x2b are the unconditional jumps
def is_branch(opcode: int) -> bool:
    return 0x2b <= opcode <= 0x44

def is_near(opcode: int) -> bool:
    return 0x2b <= opcode <= 0x37

def is_far(opcode: int) -> bool:
    return 0x38 <= opcode <= 0x44

def make_far(opcode: int) -> int:
    if is_far(opcode):
        return opcode
    return opcode+13

def make_near(opcode: int) -> int:
    if is_near(opcode):
        return opcode
    return opcode-13

def is_in_near_range(jump_addr: int, target_addr: int):
    return -128 <= target_addr - (jump_addr + 2) <= 127

# branch_delta: calculate delta from jump_addr to target_addr and encode in 1 (if near) or 4 bytes
def branch_delta(jump_addr, target_addr, near: bool) -> bytes:
    if near:
        return struct.pack("B", (target_addr - (jump_addr+2)) & 0xff)
    return struct.pack("<I", (target_addr - (jump_addr + 5)) & 0xffffffff)


# Patcher reads binary executable, applies patches, and stores to a .dec file at the end:
class Patcher(object):
    bin_data: bytes
    delta: int

    # Read binary data from disk when instantiated:
    def __init__(self):
        with open(idaapi.get_root_filename(), "rb") as f:
            self.bin_data = f.read()
        self.delta = 0
    
    # set_fct: find function code in binary data and calculate "delta" for thsi function (VA-physical mapping)
    def set_fct(self, start_va_addr: int, pattern: bytes):
        while True:
            # Somethimes instructions are skipped that sark does not see, so not the full
            # pattern need to match. Decrease until it matches.
            # TODO: Make sure match is still unique
            fct_offset = self.bin_data.find(pattern)
            if fct_offset >= 0:
                break
            pattern = pattern[:-1]
        self.delta = fct_offset - start_va_addr
    
    def write(self):
        with open(idaapi.get_root_filename() + ".dec", "wb") as f:
            f.write(self.bin_data)      

    # patch_branch: patch in a branch to the destination address at the given address.
    # if overwrite_unconditional is true, a br or br.s is encoded.
    # otherwise, the existing branch condition is kept (just made far or near if required)
    # returns the number of bytes required (5 for long, 2 for short)
    def patch_branch(self, jump_addr: int, target_addr: int, overwrite_unconditional = False) -> int:
        opcode = self.bin_data[jump_addr+self.delta]
        if overwrite_unconditional:
            opcode = 0x38  # this is a br instruction
        if not is_branch(opcode):
            print(f"ERROR: there is no branch at address {jump_addr:X}")
            return 2
    
        near = is_in_near_range(jump_addr, target_addr)
        if near:
            inst_size = 2
            opcode = make_near(opcode)
        else:
            inst_size = 5
            opcode = make_far(opcode)    
    
        self.bin_data = self.bin_data[:jump_addr + self.delta] + \
                        opcode.to_bytes(1, "little") + \
                        branch_delta(jump_addr, target_addr, near) + \
                        self.bin_data[jump_addr + self.delta + inst_size:]
        
        return inst_size
    
    def nop_inst(self, l: sark.code.line.Line):
        addr = l.ea + self.delta
        self.bin_data = self.bin_data[:addr] + (b'\x00'*l.size) + self.bin_data[addr+l.size:]
    
    def nop_code(self, l: sark.code.line.Line, end_address: int):
        while True:
            self.nop_inst(l)
            if l.ea == end_address:
                return
            if l.insn.mnem in ("br", "br.s"):
                l = sark.Line(l.insn.operands[0].addr)
                continue
            if l.insn.mnem.startswith("b"):
                self.nop_code(sark.Line(l.insn.operands[0].addr), end_address)
            l = l.next
            
       

# we collect function names that we could patch, and where patching failed:
failed: Set[str] = set()
consistent: Set[str] = set()


# SType: the different code constructs which calculate the next state variable value
class SType(Enum):
    NA = auto()
    SIMPLE = auto()       # overwrite with a new value
    MXOR = auto()         # multiplication with "mult" and xor with "xor" constant
    BRANCH = auto()       # branch combined with overwriting values
    BRANCH_MXOR = auto()  # branch combined with xor with "value"/"val_else", then multiplication with "mult"


# Suffix collect type+context of control code at the end of each block
@dataclass
class Suffix:
    addr: int = 0           # address of first control instruction
    sType: SType = SType.NA # actual code type
    val: int = -1           # value used for "if" and - for BRANCH-es - "else"
    val_else: int = -1
    xor: int = 0            # common xor/nult constants (for MXOR variants)
    mult: int = 0
    ctrls: List[sark.code.line.Line] = field(default_factory=list)  # actual control instructions (for later NOPping)
    

# Block encodes information about one switch block 
@dataclass
class Block:
    state: int              # case tag (index of block in switch, starting with 0)
    start: int              # start- and end-VA of data, excluding actual branch
    end: int = 0
    is_start: bool = False  # block sets the initial value and loop
    is_end: bool = False    # block exits loop (branch after main switch)
    is_ret: bool = False    # block hits a ret/leave instruction
    next_state = -1         # calculated next state(s), will be filled in when emulated
    next_state_else = -1
    enter_value = -1        # value of state variable when this state is entered
    enter_values: Set[int] = field(default_factory=set) # for changing enter_values, memorize all seen so far (strange cases)
    suffix = Suffix()       # used to calculate next state
    
    
@dataclass
class Switch:
    patcher: Patcher
    cont_addr: int = 0      # VA of code which calculates the next value and re-enters loop
    end_addr: int = 0       # VA of block which ends the loop (when no switch case hits), branch behind switch jumps to it
    switch_addr: int = 0    # VA of switch statement
    # entry_states gets the blocks that are initially traversed, wach with a list of jump-in addresses (usually only one)
    entry_states: Dict[int, List[int]] = field(default_factory=dict)  
    # control values for state calculation:
    xor_value: int = 0
    nbr_blocks: int = 0
    failed: bool = False    # set to true if unusual cases were detected that avoid patching
    blocks: List[Block] = field(default_factory=list)

    # next_state emulates calculation of next state variable and state
    def next_state(self, value) -> Tuple[int, int]:
        value ^= self.xor_value
        return value, value % self.nbr_blocks

    # emulate emulates switch completely (using recursion) starting with a given state. prev_block is used to update
    # the previous block "next_state..." variables, and is_else tells whether "next_state" or "next_state_else" must be changed.
    # do_print and indent are used for pretty-printing results, if required.
    # Returns True if things were fine, False on error.
    def emulate(self, state: int, value: int, prev_block: Optional[Block], do_print: bool, indent: int, is_else = False) -> bool:
        block = self.blocks[state]
        if prev_block is not None:
            if is_else:
                prev_block.next_state_else = state
            else:
                prev_block.next_state = state

        # Check if block was already traversed (loops)
        if block.next_state != -1:
            if do_print:
                print(f"{'  '*indent}{state} ^")
            # if a block is re-entered witha different state, we continue analysis, but won't try to patch anything.
            # Note: continued analysis can lead to too-many recursion levels (an upper limit could be added). 
            if block.enter_value != -1 and value != -1 and value not in block.enter_values:
                print(f"{'  '*indent}  ERROR: Inconsistent states, first time {block.enter_value:X} and now {value:X} for state {state} at VA {block.start:X}")
                self.failed = True
            else:
                block.enter_value = value
                block.enter_values.add(value)
                return True

        # Block is traversed for the first time (or analysis of dynamic blocks):
        block.enter_value = value
        block.enter_values.add(value)
        print(f"{'  '*indent}{state} [Address {block.start:X} - {block.end:X}{' START' if block.is_start else ''}{' END' if block.is_end or block.is_ret else ''}]")

        if block.is_end or block.is_ret:  # leaf 
            return True
        
        # emulate end-of-block calculation of state variable:
        if block.suffix.sType == SType.SIMPLE:
            value = block.suffix.val
            value, state = self.next_state(value)
            return self.emulate(state, value, block, do_print, indent) 
        elif block.suffix.sType == SType.MXOR:
            if value == -1:
                print(f"Uninitialized state variable at VA {block.start:X}")
                return False
            value = ((value * block.suffix.mult) & 0xffffffff) ^ block.suffix.xor
            value, state = self.next_state(value)
            return self.emulate(state, value, block, do_print, indent)
        elif block.suffix.sType == SType.BRANCH:
            value2 = block.suffix.val
            value2, state2 = self.next_state(value2)            
            print(f"{'  '*indent}IF:")
            if not self.emulate(state2,value2, block, do_print, indent+1):
                return False
            value = block.suffix.val_else
            value, state = self.next_state(value)
            print(f"{'  '*indent}ELSE:")
            return self.emulate(state, value, block, do_print, indent+1, is_else=True)
        elif block.suffix.sType == SType.BRANCH_MXOR:
            if value == -1:
                raise Exception(f"Uninitialized state variable at VA {block.start:X}")
            # value2 = ((value ^ block.suffix.val) * block.suffix.mult) & 0xffffffff
            value2 = ((value * block.suffix.mult) & 0xffffffff) ^ block.suffix.val
            value2, state2 = self.next_state(value2)            
            print(f"{'  '*indent}IF:")
            if not self.emulate(state2,value2, block, do_print, indent+1):
                return False
            # value = ((value ^ block.suffix.val_else) * block.suffix.mult) & 0xffffffff
            value = ((value * block.suffix.mult) & 0xffffffff) ^ block.suffix.val_else
            value, state = self.next_state(value)
            print(f"{'  '*indent}ELSE:")
            return self.emulate(state, value, block, do_print, indent+1, is_else=True)
        else:
            print("ERROR: Unknown suffix")        
            return False
        
    
    # patch: patch in all required branch and nop codes:
    def patch(self, lines: Dict[int, sark.code.line.Line]):
        # Entry jumps don't need to be patched:
        # for initial_state, jump_in_addrs in switch.entry_states.items():
        #     for jump_in_addr in jump_in_addrs:
        #         patch_branch(jump_in_addr, switch.blocks[initial_state].start, delta)

        # nop out switch loop as it could trigger unwanted crossreferences:
        l = lines[switch.cont_addr]
        while True:
            self.patcher.nop_inst(l)
            if is_branch(l.bytes[0]):
                break
            l = l.next
        
        for block in switch.blocks:
            if block.is_end or block.is_ret:
                continue
            
            
            # nop out all control instructions:
            for ctrl_inst in block.suffix.ctrls:
                self.patcher.nop_inst(ctrl_inst)
 
            # nop out all unusuaed states:
            if block.next_state == -1:
                print(f"INFO: block {block.state} at VA {block.:X} is unused - code will be nopped out")
                self.patcher.nop_code(lines[block.start], block.end)
                continue
            
            # and patch in branches:
            if block.next_state_else == -1:            
                # State has a unique follower (is not a branch): patch in a unconditional br instruction
                self.patcher.patch_branch(block.suffix.addr, switch.blocks[block.next_state].start, overwrite_unconditional=True)
            else:
                # State has an actual branch:
                if lines[block.suffix.addr].next.insn.mnem in ("br", "br.s"):
                    # Followed by a br/br.s: fragmentation. Long branches might not fit, so put these over subsequent ldc instructions:
                    # print(f"XX {block.suffix.addr:X} : {lines[block.suffix.addr].insn.operands[0].addr:X} --> {switch.blocks[block.next_state].start:X}")
                    # print(f"XX {block.suffix.addr:X} : {lines[block.suffix.addr].next.insn.operands[0].addr:X} --> {switch.blocks[block.next_state_else].start:X}")
                    self.patcher.patch_branch(lines[block.suffix.addr].insn.operands[0].addr, switch.blocks[block.next_state].start, overwrite_unconditional=True)
                    self.patcher.patch_branch(lines[block.suffix.addr].next.insn.operands[0].addr, switch.blocks[block.next_state_else].start, overwrite_unconditional=True)                
                else:
                    # Otherwise (2 ldc instructions follow) there is enough space for 2 branches:
                    size = self.patcher.patch_branch(block.suffix.addr, switch.blocks[block.next_state].start, overwrite_unconditional=False)
                    self.patcher.patch_branch(block.suffix.addr + size, switch.blocks[block.next_state_else].start, overwrite_unconditional=True)                


# find_suffix: traverse code from last instruction of a block backwards to detect type of control code:
def find_suffix(l: sark.code.line.Line, block_start_addr: int) -> Suffix:
    s = Suffix()
    ctrls: List[sark.code.line.Line] = []
    l2 = l
    tree_else_addr = -1  # for branches, the else part usually follows, but could be branched to as well
    prev_bytes = b''     # byte sequence of previous instruction (so actually the one behind), allows to detect 2 identical ldc instructions
    for i in range(11):  # suffixes are never longer
        if l2.insn.mnem == "switch":
            break
        ctrls.append(l2)
        if l2.ea == block_start_addr:
            break
        if tree_else_addr >= 0 and l2.insn.mnem == "ldc.i4" and l2.bytes == prev_bytes:
            # 2 identical ldc.i4 instructions detected
            prev_bytes = l2.bytes
            # after this, we jump to the else tree (linking to the pop)
            l2 = sark.Line(tree_else_addr)
            tree_else_addr = -1
            continue        
        crefs = list(l2.crefs_to)
        if len(crefs) == 1:
            prev_bytes = l2.bytes
            l2 = sark.Line(crefs[0])
            continue
        # Only instructions used in standard branch construct (b.. / ldc /  )
        if len(crefs) != 2:
            raise Exception(f"Only 1 or 2 crefs allowed at {l2.ea:X}")
        # a BRANCH combines at "pop" instruction; immediately before is the if part (2 ldc's)
        # note: theoretically, a branch cold appear in between
        if l2.insn.mnem == "pop":
            tree_else_addr = list(set(crefs)-set([l2.prev.ea]))[0]  # where the br.s of teh else part lies
            prev_bytes = l2.bytes
            l2 = l2.prev
            continue
        else:
            prev_bytes = l2.bytes
            l2 = l2.prev            
        
    if ctrls[0].insn.mnem == "ldc.i4":
        # simple constant overwrite
        s.sType = SType.SIMPLE
        s.val = l.insn.operands[0].imm
        s.addr = l.ea
        # control code if only this ldc instruction
        s.ctrls.append(ctrls[0])

    elif ctrls[0].insn.mnem == "xor" and ctrls[1].insn.mnem == "ldc.i4" and ctrls[2].insn.mnem == "mul" and \
         ctrls[3].insn.mnem == "ldc.i4" and ctrls[4].insn.mnem.startswith("ldloc."):
        s.sType = SType.MXOR
        s.xor = ctrls[1].insn.operands[0].imm
        s.mult = ctrls[3].insn.operands[0].imm
        s.addr = ctrls[4].ea
        # all 5 instructions are control instructions
        s.ctrls.extend(ctrls[0:5])

    elif ctrls[0].insn.mnem == "pop" and  ctrls[1].insn.mnem == "ldc.i4" and ctrls[2].insn.mnem == "ldc.i4" and \
         ctrls[3].insn.mnem in ("br", "br.s") and ctrls[4].insn.mnem == "ldc.i4" and ctrls[5].insn.mnem == "ldc.i4" and ctrls[6].insn.mnem.startswith("b"):
        s.sType = SType.BRANCH
        s.val = ctrls[1].insn.operands[0].imm
        s.val_else = ctrls[4].insn.operands[0].imm
        # Everything except the initial conditional jump are considered as control code. Note that the sequence usually starts with
        #   b<jj> ..., ldc
        # but sometimes (fragmentation) also with
        #   b<jj> ..., br ...
        # The if covers both with 'ctrls[6].insn.mnem.startswith("b")', but we must know where the sequence actually starts
        # (one instruction more) for correct later pathing:
        if ctrls[6].insn.mnem in ("br", "br.s"): # this is the fragmented case - we must go one instruction further back
            if ctrls[7].insn.mnem.startswith("b"):
                s.addr = ctrls[7].ea
                s.ctrls.extend(ctrls[0:6])  # test: keep br/br.s
            else:
                raise Exception(f"br should be preceeded by conditional branch at VA {ctrls[6].ea}")
        else:           
            s.addr = ctrls[6].ea
            s.ctrls.extend(ctrls[0:6])

    elif ctrls[0].insn.mnem == "xor" and ctrls[1].insn.mnem == "mul" and \
         ctrls[2].insn.mnem == "ldc.i4" and ctrls[3].insn.mnem.startswith("ldloc.") and \
         ctrls[4].insn.mnem == "pop" and  ctrls[5].insn.mnem == "ldc.i4" and ctrls[6].insn.mnem == "ldc.i4" and \
         ctrls[7].insn.mnem in ("br", "br.s") and ctrls[8].insn.mnem == "ldc.i4" and ctrls[9].insn.mnem == "ldc.i4" and ctrls[10].insn.mnem.startswith("b"):
        s.sType = SType.BRANCH_MXOR
        s.val = ctrls[5].insn.operands[0].imm
        s.val_else = ctrls[8].insn.operands[0].imm
        s.mult = ctrls[2].insn.operands[0].imm
        s.addr  = ctrls[10].ea
        # same as with normal branch
        s.ctrls.extend(ctrls[0:10])
        if ctrls[10].next.insn.mnem in ("br", "br.s"):
            s.ctrls.append(ctrls[10].next)        
    else:
        raise Exception("unknown suffix")

    return s


###
### Main code
###

patcher = Patcher()

for fct in sark.functions():
    buff: List[sark.code.line.Line] = []        # reverse order of instructions: last one at first position
    pattern = bytearray()                       # Allows us to find teh function in the binary for patching
    switches: List[Switch] = []
    lines: Dict[int, sark.code.line.Line] = {}  # code lines indexed by VA

    print(f"\nFunction {fct.name} at VA {fct.ea:X}")
    for l in fct.lines:
        buff.insert(0, l)
        lines[l.ea] = l
        ops = l.insn.operands
        pattern.extend(l.bytes)
        
        # detect switch statement with preceding modulus operation: 
        if l.insn.mnem=="switch" and buff[1].insn.mnem=="rem.un" and buff[2].insn.mnem.startswith("ldc.i4"):
            
            # 2 opcode sequences are possible: 
            #   ldc / xor / dup / stloc / ldc / rem / switch: usual case, state variable is stored as local var
            #   ldc / xor / ldc / rem / switch: in some simple cases (e.g. VA 3f1a), the state variable if kept on stack
            if len(buff) > 4 and buff[3].insn.mnem=="xor" and buff[4].insn.mnem=="ldc.i4":
                xor_value = buff[4].insn.operands[0].imm
                cont_addr = buff[4].ea  # this is where jumps to the next loop occur
            elif len(buff) > 6 and buff[5].insn.mnem=="xor" and buff[6].insn.mnem=="ldc.i4":
                xor_value = buff[6].insn.operands[0].imm
                cont_addr = buff[6].ea
            else:
                raise Exception("Unknown xor construct before switch")
            
            # number of states is pushed in the previous ldc instruction. That one can embed the immediate value into
            # the opcode for small values:
            if buff[2].insn.mnem.startswith("ldc.i4.") and len(buff[2].insn.operands) == 0:  # e.g. ldc.i4.6  (embedded operand
                nbr_blocks = int(buff[2].insn.mnem.split(".")[-1])
            else:
                nbr_blocks = buff[2].insn.operands[0].imm  # e.g. ldc.i4 100 (explixit operand)

            switch = Switch(patcher, switch_addr=l.ea, cont_addr=cont_addr, xor_value=xor_value, nbr_blocks=nbr_blocks)

            print((f"  Switch loop at VA {switch.cont_addr:X}: XOR {switch.xor_value}"))

            # The switch instruction must be followed by a branch to the exit point (when no case hits)
            if l.next.insn.mnem in ("br", "br.s"):
                switch.end_addr = l.next.insn.operands[0].addr
            else:
                raise Exception("no br after switch")
            
            # Create switch blocks for each label (we must parse these as text labels, e.g. "loc_3F47", where 3f47 is the VA)
            for state,l in enumerate(ops[0].text.split(',')):
                switch.blocks.append(Block(state, int(l.strip()[4:], 16)))
            switches.append(switch)

    # tell patcher where to find function in binary and allow it to adjust VAs to offsets:
    patcher.set_fct(fct.start_ea, pattern)    

    for switch in switches:
        start_found = False
        for block in switch.blocks:
            if block.start not in lines:
                raise Exception(f"Block address {block.start:X} has no instruction")
            l = lines[block.start]
            crefs = list(l.crefs_to)
            
            # The block that the branch after "switch" jumps to is a leaf (e.g. does not loop back):
            if switch.end_addr == l.ea:
                block.is_end = True
                block.end = l.ea  
                continue

            # We need to find the initial states. Normal states have only one xref (the switch statement itself),
            # while the initial state is also referenced by the jump-in instructions. 
            for a in crefs:
                if a not in (switch.switch_addr, switch.end_addr):
                    if lines[a].insn.mnem == "switch":
                        # if 2 switch statements link top the same state (sigh), we assume it's a common end state
                        block.is_end, block.is_start = True, False
                        break
                    if block.state not in switch.entry_states:
                        switch.entry_states[block.state] = []
                    switch.entry_states[block.state].append(a)
                    block.is_start = True
                    start_found = True
                    
            # Traverse the code for this block:
            block_lines: List[sark.code.line.Line] = []
            while True:
                # returns end the block immediately:
                if l.insn.mnem == "ret" and not block.is_end:
                    block.end = l.ea
                    block.is_end = True
                    break
                
                # embedded switch are tricky - we follow the branch behind:
                if l.insn.mnem == "switch": #... maybe we can assume these are always end nodes, but not sure...
                    l = l.next
                    if l.insn.mnem not in ("br", "br.s"):
                        print(f"  INFO: Strange embedded switch at {l.ea:X} - we assume it's an end node")
                        block.is_end, block.is_start = True, False
                        break
                    else:
                        l = lines[l.insn.operands[0].addr]
                        continue
                            
                                
                # If we hit the first instruction of the xor-part, this is the last block before, where the branch lacks:
                if l.ea == switch.cont_addr:
                    block.end = l.prev.ea
                    block.suffix = find_suffix(l.prev, block.start) # extract the next-block-constants (code suffix of block)
                    break

                # ... but most blocks end in a branch to the xor-part:
                elif l.insn.mnem in ("br", "br.s", "leave", "leave.s"):
                    if l.insn.operands[0].addr == switch.cont_addr:
                        block.end = l.prev.ea
                        block.suffix = find_suffix(l.prev, block.start)
                        # We consider the terminating branch also as control instruction:
                        block.suffix.ctrls.append(l)
                        break
                    # branches that don't return are BRANCH-type instructions that we just follow (can be fragmented)
                    l = lines[l.insn.operands[0].addr]
                    continue

                # Should not really happen (but maybe it does): last instruction of function also ends the block
                elif l.ea+l.size not in lines:
                    break

                l = lines[l.ea+l.size]
        
        if not start_found:
            print(f"  ERROR: No entry found for switch at {switch.switch_addr:X}")

        # Now we need to emulate the switch:
        for initial_state in switch.entry_states.keys():
            print(f"  Entry state {initial_state}")
            switch.failed =  not switch.emulate(initial_state, -1, None, True, 1)
                
        if switch.failed:
            failed.add(fct.name)
        else:
            consistent.add(fct.name)
            # and patch the code:
            switch.patch(lines)
        
print("Consistent functions:")
for fc in consistent:
    print(fc)

print("Failed functions:")
for fc in failed:
    print(fc)

patcher.write()

