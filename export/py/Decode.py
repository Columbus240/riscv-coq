# This Python file was autogenerated from Coq
from enum import Enum

class InstructionSet(Enum):
    RV32I = 1
    RV32IM = 2
    RV32IA = 3
    RV32IMA = 4
    RV64I = 5
    RV64IM = 6
    RV64IA = 7
    RV64IMA = 8

class InstructionM64(object): pass

class Mulw(InstructionM64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Divw(InstructionM64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Divuw(InstructionM64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Remw(InstructionM64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Remuw(InstructionM64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class InvalidM64(InstructionM64):
    def __init__(self):
        pass

class InstructionM(object): pass

class Mul(InstructionM):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Mulh(InstructionM):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Mulhsu(InstructionM):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Mulhu(InstructionM):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Div(InstructionM):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Divu(InstructionM):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Rem(InstructionM):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Remu(InstructionM):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class InvalidM(InstructionM):
    def __init__(self):
        pass

class InstructionI64(object): pass

class Ld(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Lwu(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Addiw(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Slliw(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Srliw(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sraiw(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sd(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Addw(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Subw(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sllw(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Srlw(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sraw(InstructionI64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class InvalidI64(InstructionI64):
    def __init__(self):
        pass

class InstructionI(object): pass

class Lb(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Lh(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Lw(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Lbu(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Lhu(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Fence(InstructionI):
    def __init__(self, f0, f1):
        self.f0 = f0
        self.f1 = f1

class Fence_i(InstructionI):
    def __init__(self):
        pass

class Addi(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Slli(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Slti(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sltiu(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Xori(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Ori(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Andi(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Srli(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Srai(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Auipc(InstructionI):
    def __init__(self, f0, f1):
        self.f0 = f0
        self.f1 = f1

class Sb(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sh(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sw(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Add(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sub(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sll(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Slt(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sltu(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Xor(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Srl(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sra(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Or(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class And(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Lui(InstructionI):
    def __init__(self, f0, f1):
        self.f0 = f0
        self.f1 = f1

class Beq(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Bne(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Blt(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Bge(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Bltu(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Bgeu(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Jalr(InstructionI):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Jal(InstructionI):
    def __init__(self, f0, f1):
        self.f0 = f0
        self.f1 = f1

class InvalidI(InstructionI):
    def __init__(self):
        pass

class InstructionCSR(object): pass

class Ecall(InstructionCSR):
    def __init__(self):
        pass

class Ebreak(InstructionCSR):
    def __init__(self):
        pass

class Uret(InstructionCSR):
    def __init__(self):
        pass

class Sret(InstructionCSR):
    def __init__(self):
        pass

class Mret(InstructionCSR):
    def __init__(self):
        pass

class Wfi(InstructionCSR):
    def __init__(self):
        pass

class Sfence_vma(InstructionCSR):
    def __init__(self, f0, f1):
        self.f0 = f0
        self.f1 = f1

class Csrrw(InstructionCSR):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Csrrs(InstructionCSR):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Csrrc(InstructionCSR):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Csrrwi(InstructionCSR):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Csrrsi(InstructionCSR):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Csrrci(InstructionCSR):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class InvalidCSR(InstructionCSR):
    def __init__(self):
        pass

class InstructionA64(object): pass

class Lr_d(InstructionA64):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sc_d(InstructionA64):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amoswap_d(InstructionA64):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amoadd_d(InstructionA64):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amoand_d(InstructionA64):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amoor_d(InstructionA64):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amoxor_d(InstructionA64):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amomax_d(InstructionA64):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amomaxu_d(InstructionA64):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amomin_d(InstructionA64):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amominu_d(InstructionA64):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class InvalidA64(InstructionA64):
    def __init__(self):
        pass

class InstructionA(object): pass

class Lr_w(InstructionA):
    def __init__(self, f0, f1, f2):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2

class Sc_w(InstructionA):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amoswap_w(InstructionA):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amoadd_w(InstructionA):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amoand_w(InstructionA):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amoor_w(InstructionA):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amoxor_w(InstructionA):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amomax_w(InstructionA):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amomaxu_w(InstructionA):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amomin_w(InstructionA):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class Amominu_w(InstructionA):
    def __init__(self, f0, f1, f2, f3):
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2
        self.f3 = f3

class InvalidA(InstructionA):
    def __init__(self):
        pass

class Instruction(object): pass

class IInstruction(Instruction):
    def __init__(self, f0):
        self.f0 = f0

class MInstruction(Instruction):
    def __init__(self, f0):
        self.f0 = f0

class AInstruction(Instruction):
    def __init__(self, f0):
        self.f0 = f0

class I64Instruction(Instruction):
    def __init__(self, f0):
        self.f0 = f0

class M64Instruction(Instruction):
    def __init__(self, f0):
        self.f0 = f0

class A64Instruction(Instruction):
    def __init__(self, f0):
        self.f0 = f0

class CSRInstruction(Instruction):
    def __init__(self, f0):
        self.f0 = f0

class InvalidInstruction(Instruction):
    def __init__(self, f0):
        self.f0 = f0

def bitwidth(arg_0__):
    if arg_0__ == RV32I:
        return 0b100000
    if arg_0__ == RV32IM:
        return 0b100000
    if arg_0__ == RV32IA:
        return 0b100000
    if arg_0__ == RV32IMA:
        return 0b100000
    return 0b1000000

funct12_EBREAK = 0b1

funct12_ECALL = 0b0

funct12_MRET = 0b1100000010

funct12_SRET = 0b100000010

funct12_URET = 0b10

funct12_WFI = 0b100000101

funct3_ADD = 0b0

funct3_ADDI = 0b0

funct3_ADDIW = 0b0

funct3_ADDW = 0b0

funct3_AMOD = 0b11

funct3_AMOW = 0b10

funct3_AND = 0b111

funct3_ANDI = 0b111

funct3_BEQ = 0b0

funct3_BGE = 0b101

funct3_BGEU = 0b111

funct3_BLT = 0b100

funct3_BLTU = 0b110

funct3_BNE = 0b1

funct3_CSRRC = 0b11

funct3_CSRRCI = 0b111

funct3_CSRRS = 0b10

funct3_CSRRSI = 0b110

funct3_CSRRW = 0b1

funct3_CSRRWI = 0b101

funct3_DIV = 0b100

funct3_DIVU = 0b101

funct3_DIVUW = 0b101

funct3_DIVW = 0b100

funct3_FENCE = 0b0

funct3_FENCE_I = 0b1

funct3_LB = 0b0

funct3_LBU = 0b100

funct3_LD = 0b11

funct3_LH = 0b1

funct3_LHU = 0b101

funct3_LW = 0b10

funct3_LWU = 0b110

funct3_MUL = 0b0

funct3_MULH = 0b1

funct3_MULHSU = 0b10

funct3_MULHU = 0b11

funct3_MULW = 0b0

funct3_OR = 0b110

funct3_ORI = 0b110

funct3_PRIV = 0b0

funct3_REM = 0b110

funct3_REMU = 0b111

funct3_REMUW = 0b111

funct3_REMW = 0b110

funct3_SB = 0b0

funct3_SD = 0b11

funct3_SH = 0b1

funct3_SLL = 0b1

funct3_SLLI = 0b1

funct3_SLLIW = 0b1

funct3_SLLW = 0b1

funct3_SLT = 0b10

funct3_SLTI = 0b10

funct3_SLTIU = 0b11

funct3_SLTU = 0b11

funct3_SRA = 0b101

funct3_SRAI = 0b101

funct3_SRAIW = 0b101

funct3_SRAW = 0b101

funct3_SRL = 0b101

funct3_SRLI = 0b101

funct3_SRLIW = 0b101

funct3_SRLW = 0b101

funct3_SUB = 0b0

funct3_SUBW = 0b0

funct3_SW = 0b10

funct3_XOR = 0b100

funct3_XORI = 0b100

funct5_AMOADD = 0b0

funct5_AMOAND = 0b1100

funct5_AMOMAX = 0b10100

funct5_AMOMAXU = 0b11100

funct5_AMOMIN = 0b10000

funct5_AMOMINU = 0b11000

funct5_AMOOR = 0b1000

funct5_AMOSWAP = 0b1

funct5_AMOXOR = 0b100

funct5_LR = 0b10

funct5_SC = 0b11

funct6_SLLI = 0b0

funct6_SRAI = 0b10000

funct6_SRLI = 0b0

funct7_ADD = 0b0

funct7_ADDW = 0b0

funct7_AND = 0b0

funct7_DIV = 0b1

funct7_DIVU = 0b1

funct7_DIVUW = 0b1

funct7_DIVW = 0b1

funct7_MUL = 0b1

funct7_MULH = 0b1

funct7_MULHSU = 0b1

funct7_MULHU = 0b1

funct7_MULW = 0b1

funct7_OR = 0b0

funct7_REM = 0b1

funct7_REMU = 0b1

funct7_REMUW = 0b1

funct7_REMW = 0b1

funct7_SFENCE_VMA = 0b1001

funct7_SLL = 0b0

funct7_SLLIW = 0b0

funct7_SLLW = 0b0

funct7_SLT = 0b0

funct7_SLTU = 0b0

funct7_SRA = 0b100000

funct7_SRAIW = 0b100000

funct7_SRAW = 0b100000

funct7_SRL = 0b0

funct7_SRLIW = 0b0

funct7_SRLW = 0b0

funct7_SUB = 0b100000

funct7_SUBW = 0b100000

funct7_XOR = 0b0

def isValidA(inst):
    if isinstance(inst, InvalidA):
        return False
    return True

def isValidA64(inst):
    if isinstance(inst, InvalidA64):
        return False
    return True

def isValidCSR(inst):
    if isinstance(inst, InvalidCSR):
        return False
    return True

def isValidI(inst):
    if isinstance(inst, InvalidI):
        return False
    return True

def isValidI64(inst):
    if isinstance(inst, InvalidI64):
        return False
    return True

def isValidM(inst):
    if isinstance(inst, InvalidM):
        return False
    return True

def isValidM64(inst):
    if isinstance(inst, InvalidM64):
        return False
    return True

opcode_AMO = 0b101111

opcode_AUIPC = 0b10111

opcode_BRANCH = 0b1100011

opcode_JAL = 0b1101111

opcode_JALR = 0b1100111

opcode_LOAD = 0b11

opcode_LOAD_FP = 0b111

opcode_LUI = 0b110111

opcode_MADD = 0b1000011

opcode_MISC_MEM = 0b1111

opcode_MSUB = 0b1000111

opcode_NMADD = 0b1001111

opcode_NMSUB = 0b1001011

opcode_OP = 0b110011

opcode_OP_32 = 0b111011

opcode_OP_FP = 0b1010011

opcode_OP_IMM = 0b10011

opcode_OP_IMM_32 = 0b11011

opcode_STORE = 0b100011

opcode_STORE_FP = 0b100111

opcode_SYSTEM = 0b1110011

def supportsA(arg_0__):
    if arg_0__ == RV32I:
        return False
    if arg_0__ == RV32IM:
        return False
    if arg_0__ == RV64I:
        return False
    if arg_0__ == RV64IM:
        return False
    return True

def supportsM(arg_0__):
    if arg_0__ == RV32I:
        return False
    if arg_0__ == RV32IA:
        return False
    if arg_0__ == RV64I:
        return False
    if arg_0__ == RV64IA:
        return False
    return True

def decode(iset, inst):
    aqrl = ZBitOps.bitSlice(inst, 0b11001, 0b11011)
    
    funct5 = ZBitOps.bitSlice(inst, 0b11011, 0b100000)
    
    zimm = ZBitOps.bitSlice(inst, 0b1111, 0b10100)
    
    funct6 = ZBitOps.bitSlice(inst, 0b11010, 0b100000)
    
    shamtHi = ZBitOps.bitSlice(inst, 0b11001, 0b11010)
    
    shamtHiTest = Datatypes.orb(BinInt.Z.eqb(shamtHi, 0b0), BinInt.Z.eqb(bitwidth(iset), 0b1000000))
    
    shamt6 = Utility.machineIntToShamt(ZBitOps.bitSlice(inst, 0b10100, 0b11010))
    
    shamt5 = Utility.machineIntToShamt(ZBitOps.bitSlice(inst, 0b10100, 0b11001))
    
    sbimm12 = ZBitOps.signExtend(0b1101, BinInt.Z.lor(BinInt.Z.lor(BinInt.Z.lor(BinInt.Z.shiftl(ZBitOps.bitSlice(inst, 0b11111, 0b100000), 0b1100), BinInt.Z.shiftl(ZBitOps.bitSlice(inst, 0b11001, 0b11111), 0b101)), BinInt.Z.shiftl(ZBitOps.bitSlice(inst, 0b1000, 0b1100), 0b1)), BinInt.Z.shiftl(ZBitOps.bitSlice(inst, 0b111, 0b1000), 0b1011)))
    
    simm12 = ZBitOps.signExtend(0b1100, BinInt.Z.lor(BinInt.Z.shiftl(ZBitOps.bitSlice(inst, 0b11001, 0b100000), 0b101), ZBitOps.bitSlice(inst, 0b111, 0b1100)))
    
    csr12 = ZBitOps.bitSlice(inst, 0b10100, 0b100000)
    
    oimm12 = ZBitOps.signExtend(0b1100, ZBitOps.bitSlice(inst, 0b10100, 0b100000))
    
    imm12 = ZBitOps.signExtend(0b1100, ZBitOps.bitSlice(inst, 0b10100, 0b100000))
    
    jimm20 = ZBitOps.signExtend(0b10101, BinInt.Z.lor(BinInt.Z.lor(BinInt.Z.lor(BinInt.Z.shiftl(ZBitOps.bitSlice(inst, 0b11111, 0b100000), 0b10100), BinInt.Z.shiftl(ZBitOps.bitSlice(inst, 0b10101, 0b11111), 0b1)), BinInt.Z.shiftl(ZBitOps.bitSlice(inst, 0b10100, 0b10101), 0b1011)), BinInt.Z.shiftl(ZBitOps.bitSlice(inst, 0b1100, 0b10100), 0b1100)))
    
    oimm20 = ZBitOps.signExtend(0b100000, BinInt.Z.shiftl(ZBitOps.bitSlice(inst, 0b1100, 0b100000), 0b1100))
    
    imm20 = ZBitOps.signExtend(0b100000, BinInt.Z.shiftl(ZBitOps.bitSlice(inst, 0b1100, 0b100000), 0b1100))
    
    msb4 = ZBitOps.bitSlice(inst, 0b11100, 0b100000)
    
    pred = ZBitOps.bitSlice(inst, 0b11000, 0b11100)
    
    succ = ZBitOps.bitSlice(inst, 0b10100, 0b11000)
    
    rs2 = ZBitOps.bitSlice(inst, 0b10100, 0b11001)
    
    rs1 = ZBitOps.bitSlice(inst, 0b1111, 0b10100)
    
    rd = ZBitOps.bitSlice(inst, 0b111, 0b1100)
    
    funct12 = ZBitOps.bitSlice(inst, 0b10100, 0b100000)
    
    funct7 = ZBitOps.bitSlice(inst, 0b11001, 0b100000)
    
    funct3 = ZBitOps.bitSlice(inst, 0b1100, 0b1111)
    
    opcode = ZBitOps.bitSlice(inst, 0b0, 0b111)
    
    decodeI = 