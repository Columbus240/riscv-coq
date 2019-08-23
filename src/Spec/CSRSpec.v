Require Import riscv.Spec.CSR.
Require Import riscv.Spec.CSRField.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.Utility.

Definition getCSR {M}{t}`{mach : RiscvMachine M t} (csr : CSR) : M t :=
  match csr with
   UStatus =>
