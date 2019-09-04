Require Import riscv.Spec.CSR.
Require Import riscv.Spec.CSRField.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.Utility.

Notation "a <|> b" := (Z.lor a b)
                        (at level 50, left associativity) : z_bitwise_scope.
Open Scope z_bitwise_scope.

Definition getCSR {M}{t}`{RiscvMachine M t} (csr : CSR) : M t :=
  match csr with
  | UStatus =>
    ustatus_0 <- getCSRField ustatus_0 ;
    upie <- getCSRField UPIE ;
    ustatus_1 <- getCSRField ustatus_1 ;
    uie <- getCSRField UIE ;
    Return (ZToReg (
                bitSlice uie 0 1 <|>
      Z.shiftl (bitSlice ustatus_1 0 3) 1 <|>
      Z.shiftl (bitSlice upie 0 1) 4 <|>
      Z.shiftl ustatus_0 5
    ))
  | CSR.UIE =>
    uie_0 <- getCSRField uie_0 ;
    ueie <- getCSRField UEIE ;
    uie_1 <- getCSRField uie_1 ;
    utie <- getCSRField UTIE ;
    uie_2 <- getCSRField uie_2 ;
    usie <- getCSRField USIE ;
    Return (ZToReg (
                bitSlice usie 0 1 <|>
      Z.shiftl (bitSlice uie_2 0 3) 1 <|>
      Z.shiftl (bitSlice utie 0 1) 4 <|>
      Z.shiftl (bitSlice uie_1 0 3) 5 <|>
      Z.shiftl (bitSlice ueie 0 1) 8 <|>
      Z.shiftl uie_0 9
    ))
  | UTVec =>
    base <- getCSRField UTVecBase ;
    mode <- getCSRField UTVecMode ;
    Return (ZToReg (
                bitSlice mode 0 2 <|>
      Z.shiftl base 2
    ))
  | CSR.UScratch =>
    uscratch <- getCSRField UScratch ;
    Return (ZToReg uscratch)
  | CSR.UEPC =>
    uepc <- getCSRField UEPC ;
    Return (ZToReg uepc)
  | UCause =>
    (* TODO: To be defined. *)
    Return (ZToReg 0%Z)
  | CSR.UTVal =>
    utval <- getCSRField UTVal ;
    Return (ZToReg utval)
  | CSR.UIP =>
    uip_0 <- getCSRField uip_0 ;
    ueip <- getCSRField UEIP ;
    uip_1 <- getCSRField uip_1 ;
    utip <- getCSRField UTIP ;
    uip_2 <- getCSRField uip_2 ;
    usip <- getCSRField USIP ;
    Return (ZToReg (
                bitSlice usip 0 1 <|>
      Z.shiftl (bitSlice uip_2 0 3) 1 <|>
      Z.shiftl (bitSlice utip 0 1) 4 <|>
      Z.shiftl (bitSlice uip_1 0 3) 5 <|>
      Z.shiftl (bitSlice ueip 0 1) 8 <|>
      Z.shiftl uip_0 9
    ))
  | CSR.FFlags =>
    fflags <- getCSRField FFlags ;
    Return (ZToReg (bitSlice fflags 0 5))
  | CSR.FRM =>
    frm <- getCSRField FRM ;
    Return (ZToReg (bitSlice frm 0 3))
  | FCSR =>
    fcsr_0 <- getCSRField fcsr_0 ;
    frm <- getCSRField FRM ;
    fflags <- getCSRField FFlags ;
    Return (ZToReg (
                bitSlice fflags 0 5 <|>
      Z.shiftl (bitSlice frm 0 3) 5 <|>
      Z.shiftl fcsr_0 8
    ))
  | Cycle | CSR.MCycle =>
    cycle <- getCSRField MCycle ;
    Return (ZToReg cycle)
  | Time =>
    (* TODO: To be defined. *)
    Return (ZToReg 0%Z)
  | InstRet | CSR.MInstRet =>
    instret <- getCSRField MInstRet ;
    Return (ZToReg instret)
  | CSR.MHPMCounter3 | HPMCounter3 =>
    counter <- getCSRField MHPMCounter3 ; Return (ZToReg counter)
  | CSR.MHPMCounter4 | HPMCounter4 =>
    counter <- getCSRField MHPMCounter4 ; Return (ZToReg counter)
  | CSR.MHPMCounter5 | HPMCounter5 =>
    counter <- getCSRField MHPMCounter5 ; Return (ZToReg counter)
  | CSR.MHPMCounter6 | HPMCounter6 =>
    counter <- getCSRField MHPMCounter6 ; Return (ZToReg counter)
  | CSR.MHPMCounter7 | HPMCounter7 =>
    counter <- getCSRField MHPMCounter7 ; Return (ZToReg counter)
  | CSR.MHPMCounter8 | HPMCounter8 =>
    counter <- getCSRField MHPMCounter8 ; Return (ZToReg counter)
  | CSR.MHPMCounter9 | HPMCounter9 =>
    counter <- getCSRField MHPMCounter9 ; Return (ZToReg counter)
  | CSR.MHPMCounter10 | HPMCounter10 =>
    counter <- getCSRField MHPMCounter10 ; Return (ZToReg counter)
  | CSR.MHPMCounter11 | HPMCounter11 =>
    counter <- getCSRField MHPMCounter11 ; Return (ZToReg counter)
  | CSR.MHPMCounter12 | HPMCounter12 =>
    counter <- getCSRField MHPMCounter12 ; Return (ZToReg counter)
  | CSR.MHPMCounter13 | HPMCounter13 =>
    counter <- getCSRField MHPMCounter13 ; Return (ZToReg counter)
  | CSR.MHPMCounter14 | HPMCounter14 =>
    counter <- getCSRField MHPMCounter14 ; Return (ZToReg counter)
  | CSR.MHPMCounter15 | HPMCounter15 =>
    counter <- getCSRField MHPMCounter15 ; Return (ZToReg counter)
  | CSR.MHPMCounter16 | HPMCounter16 =>
    counter <- getCSRField MHPMCounter16 ; Return (ZToReg counter)
  | CSR.MHPMCounter17 | HPMCounter17 =>
    counter <- getCSRField MHPMCounter17 ; Return (ZToReg counter)
  | CSR.MHPMCounter18 | HPMCounter18 =>
    counter <- getCSRField MHPMCounter18 ; Return (ZToReg counter)
  | CSR.MHPMCounter19 | HPMCounter19 =>
    counter <- getCSRField MHPMCounter19 ; Return (ZToReg counter)
  | CSR.MHPMCounter20 | HPMCounter20 =>
    counter <- getCSRField MHPMCounter20 ; Return (ZToReg counter)
  | CSR.MHPMCounter21 | HPMCounter21 =>
    counter <- getCSRField MHPMCounter21 ; Return (ZToReg counter)
  | CSR.MHPMCounter22 | HPMCounter22 =>
    counter <- getCSRField MHPMCounter22 ; Return (ZToReg counter)
  | CSR.MHPMCounter23 | HPMCounter23 =>
    counter <- getCSRField MHPMCounter23 ; Return (ZToReg counter)
  | CSR.MHPMCounter24 | HPMCounter24 =>
    counter <- getCSRField MHPMCounter24 ; Return (ZToReg counter)
  | CSR.MHPMCounter25 | HPMCounter25 =>
    counter <- getCSRField MHPMCounter25 ; Return (ZToReg counter)
  | CSR.MHPMCounter26 | HPMCounter26 =>
    counter <- getCSRField MHPMCounter26 ; Return (ZToReg counter)
  | CSR.MHPMCounter27 | HPMCounter27 =>
    counter <- getCSRField MHPMCounter27 ; Return (ZToReg counter)
  | CSR.MHPMCounter28 | HPMCounter28 =>
    counter <- getCSRField MHPMCounter28 ; Return (ZToReg counter)
  | CSR.MHPMCounter29 | HPMCounter29 =>
    counter <- getCSRField MHPMCounter29 ; Return (ZToReg counter)
  | CSR.MHPMCounter30 | HPMCounter30 =>
    counter <- getCSRField MHPMCounter30 ; Return (ZToReg counter)
  | CSR.MHPMCounter31 | HPMCounter31 =>
    counter <- getCSRField MHPMCounter31 ; Return (ZToReg counter)
  | CycleH | CSR.MCycleH =>
    cycle <- getCSRField MCycle ;
    Return (ZToReg (Z.shiftr cycle 32))
  | TimeH =>
    (* TODO: To be defined. *)
    Return (ZToReg 0%Z)
  | InstRetH | CSR.MInstRetH =>
    instret <- getCSRField MInstRet ;
    Return (ZToReg (Z.shiftr instret 32))
  | CSR.MHPMCounter3H | HPMCounter3H =>
    counter <- getCSRField MHPMCounter3 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter4H | HPMCounter4H =>
    counter <- getCSRField MHPMCounter4 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter5H | HPMCounter5H =>
    counter <- getCSRField MHPMCounter5 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter6H | HPMCounter6H =>
    counter <- getCSRField MHPMCounter6 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter7H | HPMCounter7H =>
    counter <- getCSRField MHPMCounter7 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter8H | HPMCounter8H =>
    counter <- getCSRField MHPMCounter8 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter9H | HPMCounter9H =>
    counter <- getCSRField MHPMCounter9 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter10H | HPMCounter10H =>
    counter <- getCSRField MHPMCounter10 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter11H | HPMCounter11H =>
    counter <- getCSRField MHPMCounter11 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter12H | HPMCounter12H =>
    counter <- getCSRField MHPMCounter12 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter13H | HPMCounter13H =>
    counter <- getCSRField MHPMCounter13 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter14H | HPMCounter14H =>
    counter <- getCSRField MHPMCounter14 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter15H | HPMCounter15H =>
    counter <- getCSRField MHPMCounter15 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter16H | HPMCounter16H =>
    counter <- getCSRField MHPMCounter16 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter17H | HPMCounter17H =>
    counter <- getCSRField MHPMCounter17 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter18H | HPMCounter18H =>
    counter <- getCSRField MHPMCounter18 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter19H | HPMCounter19H =>
    counter <- getCSRField MHPMCounter19 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter20H | HPMCounter20H =>
    counter <- getCSRField MHPMCounter20 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter21H | HPMCounter21H =>
    counter <- getCSRField MHPMCounter21 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter22H | HPMCounter22H =>
    counter <- getCSRField MHPMCounter22 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter23H | HPMCounter23H =>
    counter <- getCSRField MHPMCounter23 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter24H | HPMCounter24H =>
    counter <- getCSRField MHPMCounter24 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter25H | HPMCounter25H =>
    counter <- getCSRField MHPMCounter25 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter26H | HPMCounter26H =>
    counter <- getCSRField MHPMCounter26 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter27H | HPMCounter27H =>
    counter <- getCSRField MHPMCounter27 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter28H | HPMCounter28H =>
    counter <- getCSRField MHPMCounter28 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter29H | HPMCounter29H =>
    counter <- getCSRField MHPMCounter29 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter30H | HPMCounter30H =>
    counter <- getCSRField MHPMCounter30 ; Return (ZToReg (Z.shiftr counter 32))
  | CSR.MHPMCounter31H | HPMCounter31H =>
    counter <- getCSRField MHPMCounter31 ; Return (ZToReg (Z.shiftr counter 32))
  | SStatus =>
    (* TODO: To be defined. *)
    Return (ZToReg 0%Z)
  | CSR.SEDeleg =>
    deleg <- getCSRField SEDeleg ;
    Return (ZToReg deleg)
  | CSR.SIDeleg =>
    deleg <- getCSRField SIDeleg ;
    Return (ZToReg deleg)
  | CSR.SIE =>
    sie_0 <- getCSRField sie_0 ;
    seie <- getCSRField SEIE ;
    sie_1 <- getCSRField sie_1 ;
    stie <- getCSRField STIE ;
    sie_2 <- getCSRField sie_2 ;
    ssie <- getCSRField SSIE ;
    sie_3 <- getCSRField sie_3 ;
    Return (ZToReg (
                bitSlice sie_3 0 1 <|>
      Z.shiftl (bitSlice ssie 0 1) 1 <|>
      Z.shiftl (bitSlice sie_2 0 3) 2 <|>
      Z.shiftl (bitSlice stie 0 1) 5 <|>
      Z.shiftl (bitSlice sie_1 0 3) 6 <|>
      Z.shiftl (bitSlice seie 0 1) 9 <|>
      Z.shiftl sie_0 10
    ))
  | STVec =>
    base <- getCSRField STVecBase ;
    mode <- getCSRField STVecMode ;
    Return (ZToReg (
                bitSlice mode 0 2 <|>
      Z.shiftl base 2
    ))
  | SCounterEn =>
    shpm31 <- getCSRField SHPM31 ; shpm30 <- getCSRField SHPM30 ;
    shpm29 <- getCSRField SHPM29 ; shpm28 <- getCSRField SHPM28 ;
    shpm27 <- getCSRField SHPM27 ; shpm26 <- getCSRField SHPM26 ;
    shpm25 <- getCSRField SHPM25 ; shpm24 <- getCSRField SHPM24 ;
    shpm23 <- getCSRField SHPM23 ; shpm22 <- getCSRField SHPM22 ;
    shpm21 <- getCSRField SHPM21 ; shpm20 <- getCSRField SHPM20 ;
    shpm19 <- getCSRField SHPM19 ; shpm18 <- getCSRField SHPM18 ;
    shpm17 <- getCSRField SHPM17 ; shpm16 <- getCSRField SHPM16 ;
    shpm15 <- getCSRField SHPM15 ; shpm14 <- getCSRField SHPM14 ;
    shpm13 <- getCSRField SHPM13 ; shpm12 <- getCSRField SHPM12 ;
    shpm11 <- getCSRField SHPM11 ; shpm10 <- getCSRField SHPM10 ;
    shpm9 <- getCSRField SHPM9 ; shpm8 <- getCSRField SHPM8 ;
    shpm7 <- getCSRField SHPM7 ; shpm6 <- getCSRField SHPM6 ;
    shpm5 <- getCSRField SHPM5 ; shpm4 <- getCSRField SHPM4 ;
    shpm3 <- getCSRField SHPM3 ; sir <- getCSRField SIR ;
    stm <- getCSRField STM ; scy <- getCSRField SCY ;
    Return (ZToReg (
                bitSlice scy 0 1 <|> Z.shiftl (bitSlice stm 0 1) 1 <|>
      Z.shiftl (bitSlice sir 0 1) 2 <|> Z.shiftl (bitSlice shpm3 0 1) 3 <|>
      Z.shiftl (bitSlice shpm4 0 1) 4 <|> Z.shiftl (bitSlice shpm5 0 1) 5 <|>
      Z.shiftl (bitSlice shpm6 0 1) 6 <|> Z.shiftl (bitSlice shpm7 0 1) 7 <|>
      Z.shiftl (bitSlice shpm8 0 1) 8 <|> Z.shiftl (bitSlice shpm9 0 1) 9 <|>
      Z.shiftl (bitSlice shpm10 0 1) 10 <|> Z.shiftl (bitSlice shpm11 0 1) 11 <|>
      Z.shiftl (bitSlice shpm12 0 1) 12 <|> Z.shiftl (bitSlice shpm13 0 1) 13 <|>
      Z.shiftl (bitSlice shpm14 0 1) 14 <|> Z.shiftl (bitSlice shpm15 0 1) 15 <|>
      Z.shiftl (bitSlice shpm16 0 1) 16 <|> Z.shiftl (bitSlice shpm17 0 1) 17 <|>
      Z.shiftl (bitSlice shpm18 0 1) 18 <|> Z.shiftl (bitSlice shpm19 0 1) 19 <|>
      Z.shiftl (bitSlice shpm20 0 1) 20 <|> Z.shiftl (bitSlice shpm21 0 1) 21 <|>
      Z.shiftl (bitSlice shpm22 0 1) 22 <|> Z.shiftl (bitSlice shpm23 0 1) 23 <|>
      Z.shiftl (bitSlice shpm24 0 1) 24 <|> Z.shiftl (bitSlice shpm25 0 1) 25 <|>
      Z.shiftl (bitSlice shpm26 0 1) 26 <|> Z.shiftl (bitSlice shpm27 0 1) 27 <|>
      Z.shiftl (bitSlice shpm28 0 1) 28 <|> Z.shiftl (bitSlice shpm29 0 1) 29 <|>
      Z.shiftl (bitSlice shpm30 0 1) 30 <|> Z.shiftl (bitSlice shpm31 0 1) 31
    ))
  | CSR.SScratch =>
    sscratch <- getCSRField SScratch ;
    Return (ZToReg sscratch)
  | CSR.SEPC =>
    sepc <- getCSRField SEPC ;
    Return (ZToReg sepc)
  | SCause =>
    (* TODO: To be defined. *)
    Return (ZToReg 0%Z)
  | CSR.STVal =>
    stval <- getCSRField STVal ;
    Return (ZToReg stval)
  | CSR.SIP =>
    sip_0 <- getCSRField sip_0 ;
    seip <- getCSRField SEIP ;
    sip_1 <- getCSRField sip_1 ;
    stip <- getCSRField STIP ;
    sip_2 <- getCSRField sip_2 ;
    ssip <- getCSRField SSIP ;
    sip_3 <- getCSRField sip_3 ;
    Return (ZToReg (
                bitSlice sip_3 0 1 <|>
      Z.shiftl (bitSlice ssip 0 1) 1 <|>
      Z.shiftl (bitSlice sip_2 0 3) 2 <|>
      Z.shiftl (bitSlice stip 0 1) 5 <|>
      Z.shiftl (bitSlice sip_1 0 3) 6 <|>
      Z.shiftl (bitSlice seip 0 1) 9 <|>
      Z.shiftl sip_0 10
    ))
  | SATP =>
    (* TODO: To be defined. *)
    Return (ZToReg 0%Z)
  | MVendorID =>
    bank <- getCSRField MVendorID_Bank ;
    offset <- getCSRField MVendorID_Offset ;
    Return (ZToReg (
                bitSlice offset 0 7 <|>
      Z.shiftl (bitSlice bank 0 25) 7
    ))
  | CSR.MArchID =>
    marchid <- getCSRField MArchID ;
    Return (ZToReg marchid)
  | CSR.MImpID =>
    mimpid <- getCSRField MImpID ;
    Return (ZToReg mimpid)
  | CSR.MHartID =>
    mhartid <- getCSRField MHartID ;
    Return (ZToReg mhartid)
  | MStatus =>
    (* TODO: To be defined. *)
    Return (ZToReg 0%Z)
  | MISA =>
    (* TODO: To be defined. *)
    Return (ZToReg 0%Z)
  | CSR.MEDeleg =>
    deleg <- getCSRField MEDeleg ;
    Return (ZToReg deleg)
  | CSR.MIDeleg =>
    deleg <- getCSRField MIDeleg ;
    Return (ZToReg deleg)
  | CSR.MIE =>
    mie_0 <- getCSRField mie_0 ;
    meie <- getCSRField MEIE ;
    mie_1 <- getCSRField mie_1 ;
    seie <- getCSRField SEIE ;
    mie_2 <- getCSRField mie_2 ;
    mtie <- getCSRField MTIE ;
    mie_3 <- getCSRField mie_3 ;
    stie <- getCSRField STIE ;
    mie_4 <- getCSRField mie_4 ;
    msie <- getCSRField MSIE ;
    mie_5 <- getCSRField mie_5 ;
    ssie <- getCSRField SSIE ;
    mie_6 <- getCSRField mie_6 ;
    Return (ZToReg (
                bitSlice mie_6 0 1 <|>
      Z.shiftl (bitSlice ssie 0 1) 1 <|>
      Z.shiftl (bitSlice mie_5 0 3) 2 <|>
      Z.shiftl (bitSlice msie 0 1) 1 <|>
      Z.shiftl (bitSlice mie_4 0 3) 2 <|>
      Z.shiftl (bitSlice stie 0 1) 5 <|>
      Z.shiftl (bitSlice mie_3 0 3) 2 <|>
      Z.shiftl (bitSlice mtie 0 1) 5 <|>
      Z.shiftl (bitSlice mie_2 0 3) 6 <|>
      Z.shiftl (bitSlice seie 0 1) 9 <|>
      Z.shiftl (bitSlice mie_1 0 3) 6 <|>
      Z.shiftl (bitSlice meie 0 1) 9 <|>
      Z.shiftl mie_0 10
    ))
  | MTVec =>
    base <- getCSRField MTVecBase ;
    mode <- getCSRField MTVecMode ;
    Return (ZToReg (
                bitSlice mode 0 2 <|>
      Z.shiftl base 2
    ))
  | MCounterEn =>
    mhpm31 <- getCSRField MHPM31 ; mhpm30 <- getCSRField MHPM30 ;
    mhpm29 <- getCSRField MHPM29 ; mhpm28 <- getCSRField MHPM28 ;
    mhpm27 <- getCSRField MHPM27 ; mhpm26 <- getCSRField MHPM26 ;
    mhpm25 <- getCSRField MHPM25 ; mhpm24 <- getCSRField MHPM24 ;
    mhpm23 <- getCSRField MHPM23 ; mhpm22 <- getCSRField MHPM22 ;
    mhpm21 <- getCSRField MHPM21 ; mhpm20 <- getCSRField MHPM20 ;
    mhpm19 <- getCSRField MHPM19 ; mhpm18 <- getCSRField MHPM18 ;
    mhpm17 <- getCSRField MHPM17 ; mhpm16 <- getCSRField MHPM16 ;
    mhpm15 <- getCSRField MHPM15 ; mhpm14 <- getCSRField MHPM14 ;
    mhpm13 <- getCSRField MHPM13 ; mhpm12 <- getCSRField MHPM12 ;
    mhpm11 <- getCSRField MHPM11 ; mhpm10 <- getCSRField MHPM10 ;
    mhpm9 <- getCSRField MHPM9 ; mhpm8 <- getCSRField MHPM8 ;
    mhpm7 <- getCSRField MHPM7 ; mhpm6 <- getCSRField MHPM6 ;
    mhpm5 <- getCSRField MHPM5 ; mhpm4 <- getCSRField MHPM4 ;
    mhpm3 <- getCSRField MHPM3 ; mir <- getCSRField MIR ;
    mtm <- getCSRField MTM ; mcy <- getCSRField MCY ;
    Return (ZToReg (
                bitSlice mcy 0 1 <|> Z.shiftl (bitSlice mtm 0 1) 1 <|>
      Z.shiftl (bitSlice mir 0 1) 2 <|> Z.shiftl (bitSlice mhpm3 0 1) 3 <|>
      Z.shiftl (bitSlice mhpm4 0 1) 4 <|> Z.shiftl (bitSlice mhpm5 0 1) 5 <|>
      Z.shiftl (bitSlice mhpm6 0 1) 6 <|> Z.shiftl (bitSlice mhpm7 0 1) 7 <|>
      Z.shiftl (bitSlice mhpm8 0 1) 8 <|> Z.shiftl (bitSlice mhpm9 0 1) 9 <|>
      Z.shiftl (bitSlice mhpm10 0 1) 10 <|> Z.shiftl (bitSlice mhpm11 0 1) 11 <|>
      Z.shiftl (bitSlice mhpm12 0 1) 12 <|> Z.shiftl (bitSlice mhpm13 0 1) 13 <|>
      Z.shiftl (bitSlice mhpm14 0 1) 14 <|> Z.shiftl (bitSlice mhpm15 0 1) 15 <|>
      Z.shiftl (bitSlice mhpm16 0 1) 16 <|> Z.shiftl (bitSlice mhpm17 0 1) 17 <|>
      Z.shiftl (bitSlice mhpm18 0 1) 18 <|> Z.shiftl (bitSlice mhpm19 0 1) 19 <|>
      Z.shiftl (bitSlice mhpm20 0 1) 20 <|> Z.shiftl (bitSlice mhpm21 0 1) 21 <|>
      Z.shiftl (bitSlice mhpm22 0 1) 22 <|> Z.shiftl (bitSlice mhpm23 0 1) 23 <|>
      Z.shiftl (bitSlice mhpm24 0 1) 24 <|> Z.shiftl (bitSlice mhpm25 0 1) 25 <|>
      Z.shiftl (bitSlice mhpm26 0 1) 26 <|> Z.shiftl (bitSlice mhpm27 0 1) 27 <|>
      Z.shiftl (bitSlice mhpm28 0 1) 28 <|> Z.shiftl (bitSlice mhpm29 0 1) 29 <|>
      Z.shiftl (bitSlice mhpm30 0 1) 30 <|> Z.shiftl (bitSlice mhpm31 0 1) 31
    ))
  | MStatusH =>
    (* TODO: To be defined. *)
    Return (ZToReg 0%Z)
  | CSR.MScratch =>
    mscratch <- getCSRField MScratch ;
    Return (ZToReg mscratch)
  | CSR.MEPC =>
    mepc <- getCSRField MEPC ;
    Return (ZToReg mepc)
  | MCause =>
    (* TODO: To be defined. *)
    Return (ZToReg 0%Z)
  | CSR.MTVal =>
    mtval <- getCSRField MTVal ;
    Return (ZToReg mtval)
  | CSR.MIP =>
    mip_0 <- getCSRField mip_0 ;
    meip <- getCSRField MEIP ;
    mip_1 <- getCSRField mip_1 ;
    seip <- getCSRField SEIP ;
    mip_2 <- getCSRField mip_2 ;
    mtip <- getCSRField MTIP ;
    mip_3 <- getCSRField mip_3 ;
    stip <- getCSRField STIP ;
    mip_4 <- getCSRField mip_4 ;
    msip <- getCSRField MSIP ;
    mip_5 <- getCSRField mip_5 ;
    ssip <- getCSRField SSIP ;
    mip_6 <- getCSRField mip_6 ;
    Return (ZToReg (
                bitSlice mip_6 0 1 <|>
      Z.shiftl (bitSlice ssip 0 1) 1 <|>
      Z.shiftl (bitSlice mip_5 0 3) 2 <|>
      Z.shiftl (bitSlice msip 0 1) 1 <|>
      Z.shiftl (bitSlice mip_4 0 3) 2 <|>
      Z.shiftl (bitSlice stip 0 1) 5 <|>
      Z.shiftl (bitSlice mip_3 0 3) 2 <|>
      Z.shiftl (bitSlice mtip 0 1) 5 <|>
      Z.shiftl (bitSlice mip_2 0 3) 6 <|>
      Z.shiftl (bitSlice seip 0 1) 9 <|>
      Z.shiftl (bitSlice mip_1 0 3) 6 <|>
      Z.shiftl (bitSlice meip 0 1) 9 <|>
      Z.shiftl mip_0 10
    ))
  | PMPCfg0 | PMPCfg1 | PMPCfg2 | PMPCfg3
  | PMPAddr0 | PMPAddr1 | PMPAddr2 | PMPAddr3
  | PMPAddr4 | PMPAddr5 | PMPAddr6 | PMPAddr7
  | PMPAddr8 | PMPAddr9 | PMPAddr10 | PMPAddr11
  | PMPAddr12 | PMPAddr13 | PMPAddr14 | PMPAddr15 =>
    (* TODO: To be defined. *)
    Return (ZToReg 0%Z)
  | MCountInhibit =>
    mhpm31 <- getCSRField MHPMI31 ; mhpm30 <- getCSRField MHPMI30 ;
    mhpm29 <- getCSRField MHPMI29 ; mhpm28 <- getCSRField MHPMI28 ;
    mhpm27 <- getCSRField MHPMI27 ; mhpm26 <- getCSRField MHPMI26 ;
    mhpm25 <- getCSRField MHPMI25 ; mhpm24 <- getCSRField MHPMI24 ;
    mhpm23 <- getCSRField MHPMI23 ; mhpm22 <- getCSRField MHPMI22 ;
    mhpm21 <- getCSRField MHPMI21 ; mhpm20 <- getCSRField MHPMI20 ;
    mhpm19 <- getCSRField MHPMI19 ; mhpm18 <- getCSRField MHPMI18 ;
    mhpm17 <- getCSRField MHPMI17 ; mhpm16 <- getCSRField MHPMI16 ;
    mhpm15 <- getCSRField MHPMI15 ; mhpm14 <- getCSRField MHPMI14 ;
    mhpm13 <- getCSRField MHPMI13 ; mhpm12 <- getCSRField MHPMI12 ;
    mhpm11 <- getCSRField MHPMI11 ; mhpm10 <- getCSRField MHPMI10 ;
    mhpm9 <- getCSRField MHPMI9 ; mhpm8 <- getCSRField MHPMI8 ;
    mhpm7 <- getCSRField MHPMI7 ; mhpm6 <- getCSRField MHPMI6 ;
    mhpm5 <- getCSRField MHPMI5 ; mhpm4 <- getCSRField MHPMI4 ;
    mhpm3 <- getCSRField MHPMI3 ; mir <- getCSRField MIRI ;
    mci_0 <- getCSRField mcountinhibit_0 ; mcy <- getCSRField MCYI ;
    Return (ZToReg (
                bitSlice mcy 0 1 <|> Z.shiftl (bitSlice mci_0 0 1) 1 <|>
      Z.shiftl (bitSlice mir 0 1) 2 <|> Z.shiftl (bitSlice mhpm3 0 1) 3 <|>
      Z.shiftl (bitSlice mhpm4 0 1) 4 <|> Z.shiftl (bitSlice mhpm5 0 1) 5 <|>
      Z.shiftl (bitSlice mhpm6 0 1) 6 <|> Z.shiftl (bitSlice mhpm7 0 1) 7 <|>
      Z.shiftl (bitSlice mhpm8 0 1) 8 <|> Z.shiftl (bitSlice mhpm9 0 1) 9 <|>
      Z.shiftl (bitSlice mhpm10 0 1) 10 <|> Z.shiftl (bitSlice mhpm11 0 1) 11 <|>
      Z.shiftl (bitSlice mhpm12 0 1) 12 <|> Z.shiftl (bitSlice mhpm13 0 1) 13 <|>
      Z.shiftl (bitSlice mhpm14 0 1) 14 <|> Z.shiftl (bitSlice mhpm15 0 1) 15 <|>
      Z.shiftl (bitSlice mhpm16 0 1) 16 <|> Z.shiftl (bitSlice mhpm17 0 1) 17 <|>
      Z.shiftl (bitSlice mhpm18 0 1) 18 <|> Z.shiftl (bitSlice mhpm19 0 1) 19 <|>
      Z.shiftl (bitSlice mhpm20 0 1) 20 <|> Z.shiftl (bitSlice mhpm21 0 1) 21 <|>
      Z.shiftl (bitSlice mhpm22 0 1) 22 <|> Z.shiftl (bitSlice mhpm23 0 1) 23 <|>
      Z.shiftl (bitSlice mhpm24 0 1) 24 <|> Z.shiftl (bitSlice mhpm25 0 1) 25 <|>
      Z.shiftl (bitSlice mhpm26 0 1) 26 <|> Z.shiftl (bitSlice mhpm27 0 1) 27 <|>
      Z.shiftl (bitSlice mhpm28 0 1) 28 <|> Z.shiftl (bitSlice mhpm29 0 1) 29 <|>
      Z.shiftl (bitSlice mhpm30 0 1) 30 <|> Z.shiftl (bitSlice mhpm31 0 1) 31
    ))
  | CSR.MHPMEvent3 => event <- getCSRField MHPMEvent3 ; Return (ZToReg event)
  | CSR.MHPMEvent4 => event <- getCSRField MHPMEvent4 ; Return (ZToReg event)
  | CSR.MHPMEvent5 => event <- getCSRField MHPMEvent5 ; Return (ZToReg event)
  | CSR.MHPMEvent6 => event <- getCSRField MHPMEvent6 ; Return (ZToReg event)
  | CSR.MHPMEvent7 => event <- getCSRField MHPMEvent7 ; Return (ZToReg event)
  | CSR.MHPMEvent8 => event <- getCSRField MHPMEvent8 ; Return (ZToReg event)
  | CSR.MHPMEvent9 => event <- getCSRField MHPMEvent9 ; Return (ZToReg event)
  | CSR.MHPMEvent10 => event <- getCSRField MHPMEvent10 ; Return (ZToReg event)
  | CSR.MHPMEvent11 => event <- getCSRField MHPMEvent11 ; Return (ZToReg event)
  | CSR.MHPMEvent12 => event <- getCSRField MHPMEvent12 ; Return (ZToReg event)
  | CSR.MHPMEvent13 => event <- getCSRField MHPMEvent13 ; Return (ZToReg event)
  | CSR.MHPMEvent14 => event <- getCSRField MHPMEvent14 ; Return (ZToReg event)
  | CSR.MHPMEvent15 => event <- getCSRField MHPMEvent15 ; Return (ZToReg event)
  | CSR.MHPMEvent16 => event <- getCSRField MHPMEvent16 ; Return (ZToReg event)
  | CSR.MHPMEvent17 => event <- getCSRField MHPMEvent17 ; Return (ZToReg event)
  | CSR.MHPMEvent18 => event <- getCSRField MHPMEvent18 ; Return (ZToReg event)
  | CSR.MHPMEvent19 => event <- getCSRField MHPMEvent19 ; Return (ZToReg event)
  | CSR.MHPMEvent20 => event <- getCSRField MHPMEvent20 ; Return (ZToReg event)
  | CSR.MHPMEvent21 => event <- getCSRField MHPMEvent21 ; Return (ZToReg event)
  | CSR.MHPMEvent22 => event <- getCSRField MHPMEvent22 ; Return (ZToReg event)
  | CSR.MHPMEvent23 => event <- getCSRField MHPMEvent23 ; Return (ZToReg event)
  | CSR.MHPMEvent24 => event <- getCSRField MHPMEvent24 ; Return (ZToReg event)
  | CSR.MHPMEvent25 => event <- getCSRField MHPMEvent25 ; Return (ZToReg event)
  | CSR.MHPMEvent26 => event <- getCSRField MHPMEvent26 ; Return (ZToReg event)
  | CSR.MHPMEvent27 => event <- getCSRField MHPMEvent27 ; Return (ZToReg event)
  | CSR.MHPMEvent28 => event <- getCSRField MHPMEvent28 ; Return (ZToReg event)
  | CSR.MHPMEvent29 => event <- getCSRField MHPMEvent29 ; Return (ZToReg event)
  | CSR.MHPMEvent30 => event <- getCSRField MHPMEvent30 ; Return (ZToReg event)
  | CSR.MHPMEvent31 => event <- getCSRField MHPMEvent31 ; Return (ZToReg event)
  end.

Definition setCSR {M}{t}`{RiscvMachine M t} (csr : CSR) (val : t) : M unit :=
  match csr with
    (* TODO: Implement this. *)
  | _ => Return tt
  end.
