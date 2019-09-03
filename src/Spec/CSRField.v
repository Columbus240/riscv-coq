(* according to spec from 20th August, 2019 *)

(* I believe it is necessary to also include the WARI-fields of the
   CSR to be able to prove, that software actually ignores them. (As it
   should) *)

Inductive CSRField :=
  ustatus_0 | UPIE | ustatus_1 | UIE | (* ustatus *)
  uie_0 | UEIE | uie_1 | UTIE | uie_2 | USIE | (* uie *)
  UTVecBase | UTVecMode | (* utvec *)

  UScratch | (* uscratch *)
  UEPC | (* uepc *)
  UCauseInterrupt | UCauseCode | (* ucause *)
  UTVal | (* utval *)
  uip_0 | UEIP | uip_1 | UTIP | uip_2 | USIP | (* uip *)

  fcsr_0 | FRM | FFlags | (* fcsr, frm, fflags *)

  (* cycle(h), instret(h) and hpmcounterN(h) are read-only shadows
     of mcycle(h), minstret(h) and mhpmcounterN(h) respectively. *)
  (* time and timeh are read-only shadows of mtime, which is
     memory-mapped and thus not handled here. *)

  sstatus_0 | sstatus_1 | sstatus_2 | sstatus_3 | sstatus_4 | sstatus_5 |
  sstatus_6 | (* sstatus *)
  SEDeleg | (* sedeleg *)
  SIDeleg | (* sideleg *)
  sie_0 | sie_1 | sie_2 | sie_3 | (* sie *)
  STVecBase | STVecMode | (* stvec *)
  SHPM31 | SHPM30 | SHPM29 | SHPM28 | SHPM27 | SHPM26 | SHPM25 | SHPM24 |
  SHPM23 | SHPM22 | SHPM21 | SHPM20 | SHPM19 | SHPM18 | SHPM17 | SHPM16 |
  SHPM15 | SHPM14 | SHPM13 | SHPM12 | SHPM11 | SHPM10 | SHPM9  | SHPM8 |
  SHPM7  | SHPM6  | SHPM5  | SHPM4  | SHPM3  |
  SIR | STM | SCY | (* scounteren *)

  SScratch | (* sscratch *)
  SEPC | (* sepc *)
  SCauseInterrupt | SCauseCode | (* scause *)
  STVal | (* stval *)
  sip_0 | sip_1 | sip_2 | sip_3 | (* sip *)

  SATP_MODE | SATP_ASID | SATP_PPN | (* satp *)

  MVendorID_Bank | MVendorID_Offset | (* mvendorid *)
  MArchID | (* marchid *)
  MImpID | (* mimpid *)
  MHartID | (* mhartid *)

  SD | mstatus_0 | MBE | SBE | SXL | UXL | mstatus_1 | TSR | TW | TVM | MXR |
  SUM | MPRV | XS | FS | MPP | mstatus_2 | SPP | MPIE | UBE | SPIE | mstatus_3 |
  MIE | mstatus_4 | SIE | mstatus_5 | (* mstatus, mstatush, sstatus *)
  MXL | misa_0 | Extensions | (* misa *)
  MEDeleg | (* medeleg *)
  MIDeleg | (* mideleg *)
  mie_0 | MEIE | mie_1 | SEIE | mie_2 | MTIE | mie_3 | STIE | mie_4 | MSIE |
  mie_5 | SSIE | mie_6 | (* mie *)
  MTVecBase | MTVecMode | (* mtvec *)
  MHPM31 | MHPM30 | MHPM29 | MHPM28 | MHPM27 | MHPM26 | MHPM25 | MHPM24 |
  MHPM23 | MHPM22 | MHPM21 | MHPM20 | MHPM19 | MHPM18 | MHPM17 | MHPM16 |
  MHPM15 | MHPM14 | MHPM13 | MHPM12 | MHPM11 | MHPM10 | MHPM9  | MHPM8 |
  MHPM7  | MHPM6  | MHPM5  | MHPM4  | MHPM3  |
  MIR | MTM | MCY | (* mcounteren *)

  MScratch | (* mscratch *)
  MEPC | (* mepc *)
  MCauseInterrupt | MCauseCode | (* mcause *)
  MTVal | (* mtval *)
  mip_0 | MEIP | mip_1 | SEIP | mip_2 | MTIP | mip_3 | STIP | mip_4 | MSIP |
  mip_5 | SSIP | mip_6 | (* mip *)

  PMP0Cfg | PMP0Addr | PMP0Null |
  PMP1Cfg | PMP1Addr | PMP1Null |
  PMP2Cfg | PMP2Addr | PMP2Null |
  PMP3Cfg | PMP3Addr | PMP3Null |
  PMP4Cfg | PMP4Addr | PMP4Null |
  PMP5Cfg | PMP5Addr | PMP5Null |
  PMP6Cfg | PMP6Addr | PMP6Null |
  PMP7Cfg | PMP7Addr | PMP7Null |
  PMP8Cfg | PMP8Addr | PMP8Null |
  PMP9Cfg | PMP9Addr | PMP9Null |
  PMP10Cfg | PMP10Addr | PMP10Null |
  PMP11Cfg | PMP11Addr | PMP11Null |
  PMP12Cfg | PMP12Addr | PMP12Null |
  PMP13Cfg | PMP13Addr | PMP13Null |
  PMP14Cfg | PMP14Addr | PMP14Null |
  PMP15Cfg | PMP15Addr | PMP15Null |
  (* pmpcfg[0-3], pmpaddr[0-15] *)

  MCycle | MInstRet | (* mcycle, minstret *)
  MHPMCounter3 | (* mhpmcounterN *)
  MHPMCounter4 | MHPMCounter5 | MHPMCounter6 | MHPMCounter7 |
  MHPMCounter8 | MHPMCounter9 | MHPMCounter10 | MHPMCounter11 |
  MHPMCounter12 | MHPMCounter13 | MHPMCounter14 | MHPMCounter15 |
  MHPMCounter16 | MHPMCounter17 | MHPMCounter18 | MHPMCounter19 |
  MHPMCounter20 | MHPMCounter21 | MHPMCounter22 | MHPMCounter23 |
  MHPMCounter24 | MHPMCounter25 | MHPMCounter26 | MHPMCounter27 |
  MHPMCounter28 | MHPMCounter29 | MHPMCounter30 | MHPMCounter31 |
  MCycleH | MInstRetH | (* mcycleh, minstreth *)
  MHPMCounter3H | (* mhpmcounterNh *)
  MHPMCounter4H | MHPMCounter5H | MHPMCounter6H | MHPMCounter7H |
  MHPMCounter8H | MHPMCounter9H | MHPMCounter10H | MHPMCounter11H |
  MHPMCounter12H | MHPMCounter13H | MHPMCounter14H | MHPMCounter15H |
  MHPMCounter16H | MHPMCounter17H | MHPMCounter18H | MHPMCounter19H |
  MHPMCounter20H | MHPMCounter21H | MHPMCounter22H | MHPMCounter23H |
  MHPMCounter24H | MHPMCounter25H | MHPMCounter26H | MHPMCounter27H |
  MHPMCounter28H | MHPMCounter29H | MHPMCounter30H | MHPMCounter31H |

  MHPMI31 | MHPMI30 | MHPMI29 | MHPMI28 |
  MHPMI27 | MHPMI26 | MHPMI25 | MHPMI24 |
  MHPMI23 | MHPMI22 | MHPMI21 | MHPMI20 |
  MHPMI19 | MHPMI18 | MHPMI17 | MHPMI16 |
  MHPMI15 | MHPMI14 | MHPMI13 | MHPMI12 |
  MHPMI11 | MHPMI10 | MHPMI9  | MHPMI8 |
  MHPMI7  | MHPMI6  | MHPMI5  | MHPMI4 |
  MHPMI3  | MIRI | mcountinhibit_0 | MCYI | (* mcountinhibit *)
  MHPMEvent3 | (* mhpmeventN *)
  MHPMEvent4 | MHPMEvent5 | MHPMEvent6 | MHPMEvent7 |
  MHPMEvent8 | MHPMEvent9 | MHPMEvent10 | MHPMEvent11 |
  MHPMEvent12 | MHPMEvent13 | MHPMEvent14 | MHPMEvent15 |
  MHPMEvent16 | MHPMEvent17 | MHPMEvent18 | MHPMEvent19 |
  MHPMEvent20 | MHPMEvent21 | MHPMEvent22 | MHPMEvent23 |
  MHPMEvent24 | MHPMEvent25 | MHPMEvent26 | MHPMEvent27 |
  MHPMEvent28 | MHPMEvent29 | MHPMEvent30 | MHPMEvent31.

Inductive FieldType := RO | RW | WLRL | WARL | WPRI.

Definition fieldType (field : CSRField) : FieldType :=
  match field with
  | ustatus_0 | ustatus_1 => WPRI
  | uie_0 | uie_1 | uie_2 => WPRI
  | UTVecBase | UTVecMode => WARL

  | UEPC => WARL
  | UCauseCode => WLRL
  | UTVal => WARL
  | uip_0 | uip_1 | uip_2 => WPRI

  | fcsr_0 => WPRI

  | sstatus_0 | sstatus_1 | sstatus_2 | sstatus_3
  | sstatus_4 | sstatus_5 | sstatus_6 => WPRI
  | SEDeleg => WARL
  | SIDeleg => WARL
  | sie_0 | sie_1 | sie_2 | sie_3 => WPRI
  | STVecBase | STVecMode => WARL
  | SHPM31 | SHPM30 | SHPM29 | SHPM28 | SHPM27 | SHPM26 | SHPM25 | SHPM24
  | SHPM23 | SHPM22 | SHPM21 | SHPM20 | SHPM19 | SHPM18 | SHPM17 | SHPM16
  | SHPM15 | SHPM14 | SHPM13 | SHPM12 | SHPM11 | SHPM10 | SHPM9  | SHPM8
  | SHPM7  | SHPM6  | SHPM5  | SHPM4  | SHPM3  | SIR | STM | SCY => WARL

  | SEPC => WARL
  | SCauseCode => WLRL
  | STVal => WARL
  | sip_0 | sip_1 | sip_2 | sip_3 => WPRI

  | SATP_MODE | SATP_ASID | SATP_PPN => WARL

  | MVendorID_Bank | MVendorID_Offset => RO
  | MArchID => RO
  | MImpID => RO
  | MHartID => RO

  | SD => RO
  | MBE | SBE => WARL
  | SXL | UXL => WARL
  | TSR | TW | TVM => WARL
  | XS => RO
  | FS => WARL
  | MPP => WARL
  | SPP => WARL
  | UBE => WARL
  | mstatus_0 | mstatus_1 | mstatus_2 | mstatus_3
  | mstatus_4 | mstatus_5 => WPRI
  | MXL | Extensions => WARL
  | misa_0 => WLRL
  | MEDeleg => WARL
  | MIDeleg => WARL
  | mie_0 | mie_1 | mie_2 | mie_3 | mie_4 | mie_5 | mie_6 => WPRI
  | MTVecBase | MTVecMode => WARL
  | MHPM31 | MHPM30 | MHPM29 | MHPM28 | MHPM27 | MHPM26 | MHPM25 | MHPM24
  | MHPM23 | MHPM22 | MHPM21 | MHPM20 | MHPM19 | MHPM18 | MHPM17 | MHPM16
  | MHPM15 | MHPM14 | MHPM13 | MHPM12 | MHPM11 | MHPM10 | MHPM9  | MHPM8
  | MHPM7  | MHPM6  | MHPM5  | MHPM4  | MHPM3 | MIR | MTM | MCY => WARL

  | MEPC => WARL
  | MCauseCode => WLRL
  | MTVal => WARL
  | mip_0 | mip_1 | mip_2 | mip_3 | mip_4 | mip_5 | mip_6 => WPRI

  | PMP0Cfg | PMP0Addr | PMP0Null
  | PMP1Cfg | PMP1Addr | PMP1Null
  | PMP2Cfg | PMP2Addr | PMP2Null
  | PMP3Cfg | PMP3Addr | PMP3Null
  | PMP4Cfg | PMP4Addr | PMP4Null
  | PMP5Cfg | PMP5Addr | PMP5Null
  | PMP6Cfg | PMP6Addr | PMP6Null
  | PMP7Cfg | PMP7Addr | PMP7Null
  | PMP8Cfg | PMP8Addr | PMP8Null
  | PMP9Cfg | PMP9Addr | PMP9Null
  | PMP10Cfg | PMP10Addr | PMP10Null
  | PMP11Cfg | PMP11Addr | PMP11Null
  | PMP12Cfg | PMP12Addr | PMP12Null
  | PMP13Cfg | PMP13Addr | PMP13Null
  | PMP14Cfg | PMP14Addr | PMP14Null
  | PMP15Cfg | PMP15Addr | PMP15Null => WARL

  | MHPMI31 | MHPMI30 | MHPMI29 | MHPMI28
  | MHPMI27 | MHPMI26 | MHPMI25 | MHPMI24
  | MHPMI23 | MHPMI22 | MHPMI21 | MHPMI20
  | MHPMI19 | MHPMI18 | MHPMI17 | MHPMI16
  | MHPMI15 | MHPMI14 | MHPMI13 | MHPMI12
  | MHPMI11 | MHPMI10 | MHPMI9  | MHPMI8
  | MHPMI7  | MHPMI6  | MHPMI5  | MHPMI4
  | MHPMI3  | MIRI | MCYI => WARL
  | mcountinhibit_0 => WPRI
  | MHPMEvent3
  | MHPMEvent4 | MHPMEvent5 | MHPMEvent6 | MHPMEvent7
  | MHPMEvent8 | MHPMEvent9 | MHPMEvent10 | MHPMEvent11
  | MHPMEvent12 | MHPMEvent13 | MHPMEvent14 | MHPMEvent15
  | MHPMEvent16 | MHPMEvent17 | MHPMEvent18 | MHPMEvent19
  | MHPMEvent20 | MHPMEvent21 | MHPMEvent22 | MHPMEvent23
  | MHPMEvent24 | MHPMEvent25 | MHPMEvent26 | MHPMEvent27
  | MHPMEvent28 | MHPMEvent29 | MHPMEvent30 | MHPMEvent31 => WARL

  | _ => RW
  end.
