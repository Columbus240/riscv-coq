Require Import coqutil.Z.HexNotation.

Require Import riscv.Utility.Utility.

(* Alternate formalisations:
   Put RV32I-only CSRs in their own type. See Spec.Decode.Instruction for an
   example.
   Might make it easier to formalise RV64I or RV128I.

   Grouping by privilege-level (MRO, MRW, …) might also be a
   reasonable because it might simplify checking access permissions.
*)

Inductive CSR :=
  (* ** User-Level CSRs ** *)
  (* User Trap Setup *)
  UStatus | UIE | UTVec |
  (* User Trap Handling *)
  UScratch | UEPC | UCause | UTVal | UIP |
  (* User Floating-Point CSRs *)
  FFlags | FRM | FCSR |
  (* User Counter/Timers *)
  Cycle | Time | InstRet |
  HPMCounter3 |
  HPMCounter4 | HPMCounter5 | HPMCounter6 | HPMCounter7 |
  HPMCounter8 | HPMCounter9 | HPMCounter10 | HPMCounter11 |
  HPMCounter12 | HPMCounter13 | HPMCounter14 | HPMCounter15 |
  HPMCounter16 | HPMCounter17 | HPMCounter18 | HPMCounter19 |
  HPMCounter20 | HPMCounter21 | HPMCounter22 | HPMCounter23 |
  HPMCounter24 | HPMCounter25 | HPMCounter26 | HPMCounter27 |
  HPMCounter28 | HPMCounter29 | HPMCounter30 | HPMCounter31 |
  CycleH | TimeH | InstRetH |
  HPMCounter3H |
  HPMCounter4H | HPMCounter5H | HPMCounter6H | HPMCounter7H |
  HPMCounter8H | HPMCounter9H | HPMCounter10H | HPMCounter11H |
  HPMCounter12H | HPMCounter13H | HPMCounter14H | HPMCounter15H |
  HPMCounter16H | HPMCounter17H | HPMCounter18H | HPMCounter19H |
  HPMCounter20H | HPMCounter21H | HPMCounter22H | HPMCounter23H |
  HPMCounter24H | HPMCounter25H | HPMCounter26H | HPMCounter27H |
  HPMCounter28H | HPMCounter29H | HPMCounter30H | HPMCounter31H |

  (* ** Supervisor-Level CSRs ** *)
  (* Supervisor Trap Setup *)
  SStatus | SEDeleg | SIDeleg | SIE | STVec | SCounterEn |
  (* Supervisor Trap Handling *)
  SScratch | SEPC | SCause | STVal | SIP |
  (* Supervisor Protection and Translation *)
  SATP |

  (* ** Machine-Level CSRs ** *)
  (* Machine Information Registers *)
  MVendorID | MArchID | MImpID | MHartID |
  (* Machine Trap Setup *)
  MStatus | MISA | MEDeleg | MIDeleg | MIE | MTVec | MCounterEn | MStatusH |
  (* Machine Trap Handling *)
  MScratch | MEPC | MCause | MTVal | MIP |
  (* Machine Memory Protection *)
  PMPCfg0 | PMPCfg1 | PMPCfg2 | PMPCfg3 |
  PMPAddr0 | PMPAddr1 | PMPAddr2 | PMPAddr3 |
  PMPAddr4 | PMPAddr5 | PMPAddr6 | PMPAddr7 |
  PMPAddr8 | PMPAddr9 | PMPAddr10 | PMPAddr11 |
  PMPAddr12 | PMPAddr13 | PMPAddr14 | PMPAddr15 |
  (* Machine Counter/Timers *)
  MCycle | MInstRet |
  MHPMCounter3 |
  MHPMCounter4 | MHPMCounter5 | MHPMCounter6 | MHPMCounter7 |
  MHPMCounter8 | MHPMCounter9 | MHPMCounter10 | MHPMCounter11 |
  MHPMCounter12 | MHPMCounter13 | MHPMCounter14 | MHPMCounter15 |
  MHPMCounter16 | MHPMCounter17 | MHPMCounter18 | MHPMCounter19 |
  MHPMCounter20 | MHPMCounter21 | MHPMCounter22 | MHPMCounter23 |
  MHPMCounter24 | MHPMCounter25 | MHPMCounter26 | MHPMCounter27 |
  MHPMCounter28 | MHPMCounter29 | MHPMCounter30 | MHPMCounter31 |
  MCycleH | MInstRetH |
  MHPMCounter3H |
  MHPMCounter4H | MHPMCounter5H | MHPMCounter6H | MHPMCounter7H |
  MHPMCounter8H | MHPMCounter9H | MHPMCounter10H | MHPMCounter11H |
  MHPMCounter12H | MHPMCounter13H | MHPMCounter14H | MHPMCounter15H |
  MHPMCounter16H | MHPMCounter17H | MHPMCounter18H | MHPMCounter19H |
  MHPMCounter20H | MHPMCounter21H | MHPMCounter22H | MHPMCounter23H |
  MHPMCounter24H | MHPMCounter25H | MHPMCounter26H | MHPMCounter27H |
  MHPMCounter28H | MHPMCounter29H | MHPMCounter30H | MHPMCounter31H |
  (* Machine Counter Setup *)
  MCountInhibit |
  MHPMEvent3 |
  MHPMEvent4 | MHPMEvent5 | MHPMEvent6 | MHPMEvent7 |
  MHPMEvent8 | MHPMEvent9 | MHPMEvent10 | MHPMEvent11 |
  MHPMEvent12 | MHPMEvent13 | MHPMEvent14 | MHPMEvent15 |
  MHPMEvent16 | MHPMEvent17 | MHPMEvent18 | MHPMEvent19 |
  MHPMEvent20 | MHPMEvent21 | MHPMEvent22 | MHPMEvent23 |
  MHPMEvent24 | MHPMEvent25 | MHPMEvent26 | MHPMEvent27 |
  MHPMEvent28 | MHPMEvent29 | MHPMEvent30 | MHPMEvent31 |
  (* Debug/Trace Registers (shared with Debug Mode) *)
  TSelect | TData1 | TData2 | TData3 |
  (* Debug Mode Registers *)
  DCSR | DPC | DScratch0 | DScratch1.

(* Possible optimisation: Use a datastructure to improve lookup
   speed. *)
Definition lookupCSR (x : MachineInt) : option CSR :=
  if Z.eqb x (Ox"000") then
    Some UStatus
  else if Z.eqb x (Ox"004") then
    Some UIE
  else if Z.eqb x (Ox"005") then
    Some UTVec
  (**)
  else if Z.eqb x (Ox"040") then
    Some UScratch
  else if Z.eqb x (Ox"041") then
    Some UEPC
  else if Z.eqb x (Ox"042") then
    Some UCause
  else if Z.eqb x (Ox"043") then
    Some UTVal
  else if Z.eqb x (Ox"044") then
    Some UIP
  (**)
  else if Z.eqb x (Ox"001") then
    Some FFlags
  else if Z.eqb x (Ox"002") then
    Some FRM
  else if Z.eqb x (Ox"003") then
    Some FCSR
  (**)
  else if Z.eqb x (Ox"C00") then
    Some Cycle
  else if Z.eqb x (Ox"C01") then
    Some Time
  else if Z.eqb x (Ox"C02") then
    Some InstRet
  else if Z.eqb x (Ox"C03") then
    Some HPMCounter3
  else if Z.eqb x (Ox"C04") then
    Some HPMCounter4
  else if Z.eqb x (Ox"C05") then
    Some HPMCounter5
  else if Z.eqb x (Ox"C06") then
    Some HPMCounter6
  else if Z.eqb x (Ox"C07") then
    Some HPMCounter7
  else if Z.eqb x (Ox"C08") then
    Some HPMCounter8
  else if Z.eqb x (Ox"C09") then
    Some HPMCounter9
  else if Z.eqb x (Ox"C0A") then
    Some HPMCounter10
  else if Z.eqb x (Ox"C0B") then
    Some HPMCounter11
  else if Z.eqb x (Ox"C0C") then
    Some HPMCounter12
  else if Z.eqb x (Ox"C0D") then
    Some HPMCounter13
  else if Z.eqb x (Ox"C0E") then
    Some HPMCounter14
  else if Z.eqb x (Ox"C0F") then
    Some HPMCounter15
  else if Z.eqb x (Ox"C10") then
    Some HPMCounter16
  else if Z.eqb x (Ox"C11") then
    Some HPMCounter17
  else if Z.eqb x (Ox"C12") then
    Some HPMCounter18
  else if Z.eqb x (Ox"C13") then
    Some HPMCounter19
  else if Z.eqb x (Ox"C14") then
    Some HPMCounter20
  else if Z.eqb x (Ox"C15") then
    Some HPMCounter21
  else if Z.eqb x (Ox"C16") then
    Some HPMCounter22
  else if Z.eqb x (Ox"C17") then
    Some HPMCounter23
  else if Z.eqb x (Ox"C18") then
    Some HPMCounter24
  else if Z.eqb x (Ox"C19") then
    Some HPMCounter25
  else if Z.eqb x (Ox"C1A") then
    Some HPMCounter26
  else if Z.eqb x (Ox"C1B") then
    Some HPMCounter27
  else if Z.eqb x (Ox"C1C") then
    Some HPMCounter28
  else if Z.eqb x (Ox"C1D") then
    Some HPMCounter29
  else if Z.eqb x (Ox"C1E") then
    Some HPMCounter30
  else if Z.eqb x (Ox"C1F") then
    Some HPMCounter31
  else if Z.eqb x (Ox"C80") then
    Some CycleH
  else if Z.eqb x (Ox"C81") then
    Some TimeH
  else if Z.eqb x (Ox"C82") then
    Some InstRetH
  else if Z.eqb x (Ox"C83") then
    Some HPMCounter3H
  else if Z.eqb x (Ox"C84") then
    Some HPMCounter4H
  else if Z.eqb x (Ox"C85") then
    Some HPMCounter5H
  else if Z.eqb x (Ox"C86") then
    Some HPMCounter6H
  else if Z.eqb x (Ox"C87") then
    Some HPMCounter7H
  else if Z.eqb x (Ox"C88") then
    Some HPMCounter8H
  else if Z.eqb x (Ox"C89") then
    Some HPMCounter9H
  else if Z.eqb x (Ox"C8A") then
    Some HPMCounter10H
  else if Z.eqb x (Ox"C8B") then
    Some HPMCounter11H
  else if Z.eqb x (Ox"C8C") then
    Some HPMCounter12H
  else if Z.eqb x (Ox"C8D") then
    Some HPMCounter13H
  else if Z.eqb x (Ox"C8E") then
    Some HPMCounter14H
  else if Z.eqb x (Ox"C8F") then
    Some HPMCounter15H
  else if Z.eqb x (Ox"C80") then
    Some HPMCounter16H
  else if Z.eqb x (Ox"C81") then
    Some HPMCounter17H
  else if Z.eqb x (Ox"C82") then
    Some HPMCounter18H
  else if Z.eqb x (Ox"C83") then
    Some HPMCounter19H
  else if Z.eqb x (Ox"C84") then
    Some HPMCounter20H
  else if Z.eqb x (Ox"C85") then
    Some HPMCounter21H
  else if Z.eqb x (Ox"C86") then
    Some HPMCounter22H
  else if Z.eqb x (Ox"C87") then
    Some HPMCounter23H
  else if Z.eqb x (Ox"C88") then
    Some HPMCounter24H
  else if Z.eqb x (Ox"C89") then
    Some HPMCounter25H
  else if Z.eqb x (Ox"C8A") then
    Some HPMCounter26H
  else if Z.eqb x (Ox"C8B") then
    Some HPMCounter27H
  else if Z.eqb x (Ox"C8C") then
    Some HPMCounter28H
  else if Z.eqb x (Ox"C8D") then
    Some HPMCounter29H
  else if Z.eqb x (Ox"C8E") then
    Some HPMCounter30H
  else if Z.eqb x (Ox"C8F") then
    Some HPMCounter31H
  (**)
  else if Z.eqb x (Ox"100") then
    Some SStatus
  else if Z.eqb x (Ox"102") then
    Some SEDeleg
  else if Z.eqb x (Ox"103") then
    Some SIDeleg
  else if Z.eqb x (Ox"104") then
    Some SIE
  else if Z.eqb x (Ox"105") then
    Some STVec
  else if Z.eqb x (Ox"106") then
    Some SCounterEn
  (**)
  else if Z.eqb x (Ox"140") then
    Some SScratch
  else if Z.eqb x (Ox"141") then
    Some SEPC
  else if Z.eqb x (Ox"142") then
    Some SCause
  else if Z.eqb x (Ox"143") then
    Some STVal
  else if Z.eqb x (Ox"144") then
    Some SIP
  (**)
  else if Z.eqb x (Ox"180") then
    Some SATP
  (**)
  else if Z.eqb x (Ox"F11") then
    Some MVendorID
  else if Z.eqb x (Ox"F12") then
    Some MArchID
  else if Z.eqb x (Ox"F13") then
    Some MImpID
  else if Z.eqb x (Ox"F14") then
    Some MHartID
  (**)
  else if Z.eqb x (Ox"300") then
    Some MStatus
  else if Z.eqb x (Ox"301") then
    Some MISA
  else if Z.eqb x (Ox"302") then
    Some MEDeleg
  else if Z.eqb x (Ox"303") then
    Some MIDeleg
  else if Z.eqb x (Ox"304") then
    Some MIE
  else if Z.eqb x (Ox"305") then
    Some MTVec
  else if Z.eqb x (Ox"306") then
    Some MCounterEn
  else if Z.eqb x (Ox"310") then
    Some MStatusH
  (**)
  else if Z.eqb x (Ox"340") then
    Some MScratch
  else if Z.eqb x (Ox"341") then
    Some MEPC
  else if Z.eqb x (Ox"342") then
    Some MCause
  else if Z.eqb x (Ox"343") then
    Some MTVal
  else if Z.eqb x (Ox"344") then
    Some MIP
  (**)
  else if Z.eqb x (Ox"3A0") then
    Some PMPCfg0
  else if Z.eqb x (Ox"3A1") then
    Some PMPCfg1
  else if Z.eqb x (Ox"3A2") then
    Some PMPCfg2
  else if Z.eqb x (Ox"3A3") then
    Some PMPCfg3
  else if Z.eqb x (Ox"3B0") then
    Some PMPAddr0
  else if Z.eqb x (Ox"3B1") then
    Some PMPAddr1
  else if Z.eqb x (Ox"3B2") then
    Some PMPAddr2
  else if Z.eqb x (Ox"3B3") then
    Some PMPAddr3
  else if Z.eqb x (Ox"3B4") then
    Some PMPAddr4
  else if Z.eqb x (Ox"3B5") then
    Some PMPAddr5
  else if Z.eqb x (Ox"3B6") then
    Some PMPAddr6
  else if Z.eqb x (Ox"3B7") then
    Some PMPAddr7
  else if Z.eqb x (Ox"3B8") then
    Some PMPAddr8
  else if Z.eqb x (Ox"3B9") then
    Some PMPAddr9
  else if Z.eqb x (Ox"3BA") then
    Some PMPAddr10
  else if Z.eqb x (Ox"3BB") then
    Some PMPAddr11
  else if Z.eqb x (Ox"3BC") then
    Some PMPAddr12
  else if Z.eqb x (Ox"3BD") then
    Some PMPAddr13
  else if Z.eqb x (Ox"3BE") then
    Some PMPAddr14
  else if Z.eqb x (Ox"3BF") then
    Some PMPAddr15
  (**)
  else if Z.eqb x (Ox"B00") then
    Some MCycle
  else if Z.eqb x (Ox"B02") then
    Some MInstRet
  else if Z.eqb x (Ox"B03") then
    Some MHPMCounter3
  else if Z.eqb x (Ox"B04") then
    Some MHPMCounter4
  else if Z.eqb x (Ox"B05") then
    Some MHPMCounter5
  else if Z.eqb x (Ox"B06") then
    Some MHPMCounter6
  else if Z.eqb x (Ox"B07") then
    Some MHPMCounter7
  else if Z.eqb x (Ox"B08") then
    Some MHPMCounter8
  else if Z.eqb x (Ox"B09") then
    Some MHPMCounter9
  else if Z.eqb x (Ox"B0A") then
    Some MHPMCounter10
  else if Z.eqb x (Ox"B0B") then
    Some MHPMCounter11
  else if Z.eqb x (Ox"B0C") then
    Some MHPMCounter12
  else if Z.eqb x (Ox"B0D") then
    Some MHPMCounter13
  else if Z.eqb x (Ox"B0E") then
    Some MHPMCounter14
  else if Z.eqb x (Ox"B0F") then
    Some MHPMCounter15
  else if Z.eqb x (Ox"B10") then
    Some MHPMCounter16
  else if Z.eqb x (Ox"B11") then
    Some MHPMCounter17
  else if Z.eqb x (Ox"B12") then
    Some MHPMCounter18
  else if Z.eqb x (Ox"B13") then
    Some MHPMCounter19
  else if Z.eqb x (Ox"B14") then
    Some MHPMCounter20
  else if Z.eqb x (Ox"B15") then
    Some MHPMCounter21
  else if Z.eqb x (Ox"B16") then
    Some MHPMCounter22
  else if Z.eqb x (Ox"B17") then
    Some MHPMCounter23
  else if Z.eqb x (Ox"B18") then
    Some MHPMCounter24
  else if Z.eqb x (Ox"B19") then
    Some MHPMCounter25
  else if Z.eqb x (Ox"B1A") then
    Some MHPMCounter26
  else if Z.eqb x (Ox"B1B") then
    Some MHPMCounter27
  else if Z.eqb x (Ox"B1C") then
    Some MHPMCounter28
  else if Z.eqb x (Ox"B1D") then
    Some MHPMCounter29
  else if Z.eqb x (Ox"B1E") then
    Some MHPMCounter30
  else if Z.eqb x (Ox"B1F") then
    Some MHPMCounter31
  else if Z.eqb x (Ox"B80") then
    Some MCycleH
  else if Z.eqb x (Ox"B82") then
    Some MInstRetH
  else if Z.eqb x (Ox"B83") then
    Some MHPMCounter3H
  else if Z.eqb x (Ox"B84") then
    Some MHPMCounter4H
  else if Z.eqb x (Ox"B85") then
    Some MHPMCounter5H
  else if Z.eqb x (Ox"B86") then
    Some MHPMCounter6H
  else if Z.eqb x (Ox"B87") then
    Some MHPMCounter7H
  else if Z.eqb x (Ox"B88") then
    Some MHPMCounter8H
  else if Z.eqb x (Ox"B89") then
    Some MHPMCounter9H
  else if Z.eqb x (Ox"B8A") then
    Some MHPMCounter10H
  else if Z.eqb x (Ox"B8B") then
    Some MHPMCounter11H
  else if Z.eqb x (Ox"B8C") then
    Some MHPMCounter12H
  else if Z.eqb x (Ox"B8D") then
    Some MHPMCounter13H
  else if Z.eqb x (Ox"B8E") then
    Some MHPMCounter14H
  else if Z.eqb x (Ox"B8F") then
    Some MHPMCounter15H
  else if Z.eqb x (Ox"B90") then
    Some MHPMCounter16H
  else if Z.eqb x (Ox"B91") then
    Some MHPMCounter17H
  else if Z.eqb x (Ox"B92") then
    Some MHPMCounter18H
  else if Z.eqb x (Ox"B93") then
    Some MHPMCounter19H
  else if Z.eqb x (Ox"B94") then
    Some MHPMCounter20H
  else if Z.eqb x (Ox"B95") then
    Some MHPMCounter21H
  else if Z.eqb x (Ox"B96") then
    Some MHPMCounter22H
  else if Z.eqb x (Ox"B97") then
    Some MHPMCounter23H
  else if Z.eqb x (Ox"B98") then
    Some MHPMCounter24H
  else if Z.eqb x (Ox"B99") then
    Some MHPMCounter25H
  else if Z.eqb x (Ox"B9A") then
    Some MHPMCounter26H
  else if Z.eqb x (Ox"B9B") then
    Some MHPMCounter27H
  else if Z.eqb x (Ox"B9C") then
    Some MHPMCounter28H
  else if Z.eqb x (Ox"B9D") then
    Some MHPMCounter29H
  else if Z.eqb x (Ox"B9E") then
    Some MHPMCounter30H
  else if Z.eqb x (Ox"B9F") then
    Some MHPMCounter31H
   (**)
  else if Z.eqb x (Ox"320") then
    Some MCountInhibit
  else if Z.eqb x (Ox"323") then
    Some MHPMEvent3
  else if Z.eqb x (Ox"324") then
    Some MHPMEvent4
  else if Z.eqb x (Ox"325") then
    Some MHPMEvent5
  else if Z.eqb x (Ox"326") then
    Some MHPMEvent6
  else if Z.eqb x (Ox"327") then
    Some MHPMEvent7
  else if Z.eqb x (Ox"328") then
    Some MHPMEvent8
  else if Z.eqb x (Ox"329") then
    Some MHPMEvent9
  else if Z.eqb x (Ox"32A") then
    Some MHPMEvent10
  else if Z.eqb x (Ox"32B") then
    Some MHPMEvent11
  else if Z.eqb x (Ox"32C") then
    Some MHPMEvent12
  else if Z.eqb x (Ox"32D") then
    Some MHPMEvent13
  else if Z.eqb x (Ox"32E") then
    Some MHPMEvent14
  else if Z.eqb x (Ox"32F") then
    Some MHPMEvent15
  else if Z.eqb x (Ox"330") then
    Some MHPMEvent16
  else if Z.eqb x (Ox"331") then
    Some MHPMEvent17
  else if Z.eqb x (Ox"332") then
    Some MHPMEvent18
  else if Z.eqb x (Ox"333") then
    Some MHPMEvent19
  else if Z.eqb x (Ox"334") then
    Some MHPMEvent20
  else if Z.eqb x (Ox"335") then
    Some MHPMEvent21
  else if Z.eqb x (Ox"336") then
    Some MHPMEvent22
  else if Z.eqb x (Ox"337") then
    Some MHPMEvent23
  else if Z.eqb x (Ox"338") then
    Some MHPMEvent24
  else if Z.eqb x (Ox"339") then
    Some MHPMEvent25
  else if Z.eqb x (Ox"33A") then
    Some MHPMEvent26
  else if Z.eqb x (Ox"33B") then
    Some MHPMEvent27
  else if Z.eqb x (Ox"33C") then
    Some MHPMEvent28
  else if Z.eqb x (Ox"33D") then
    Some MHPMEvent29
  else if Z.eqb x (Ox"33E") then
    Some MHPMEvent30
  else if Z.eqb x (Ox"33F") then
    Some MHPMEvent31
  (**)
  else if Z.eqb x (Ox"7A0") then
    Some TSelect
  else if Z.eqb x (Ox"7A1") then
    Some TData1
  else if Z.eqb x (Ox"7A2") then
    Some TData2
  else if Z.eqb x (Ox"7A3") then
    Some TData3
  (**)
  else if Z.eqb x (Ox"7B0") then
    Some DCSR
  else if Z.eqb x (Ox"7B1") then
    Some DPC
  else if Z.eqb x (Ox"7B2") then
    Some DScratch0
  else if Z.eqb x (Ox"7B3") then
    Some DScratch1
  (**)
  else
    None.
