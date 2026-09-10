Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.

Definition zesuEncoderOptionalU64SomeCallSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_c_call 32
    (fun args sp RET =>
      ∃ (value : bv 64) (tag : bv 8) (tail : spec),
      bv_unsigned (args !!! 0%nat) ↦ₘ value ∗
      (bv_unsigned (args !!! 0%nat) + 8) ↦ₘ tag ∗
      ⌜tag ≠ BV 8 0⌝ ∗
      ⌜bv_extract 0 3 (args !!! 0%nat) = BV 3 0⌝ ∗
      ⌜0x20000000 <= bv_unsigned (args !!! 0%nat)⌝ ∗
      ⌜bv_unsigned (args !!! 0%nat) + 8 < 0x40000000⌝ ∗
      mmio_range 0x2401a0c0 16 ∗
      spec_trace
        (writeOutputEvents (sp - BV 64 16 - BV 64 16 + BV 64 7)%bv
          (BV 64 1)
          (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail)) ∗
      RET (fun _ =>
        bv_unsigned (args !!! 0%nat) ↦ₘ value ∗
        (bv_unsigned (args !!! 0%nat) + 8) ↦ₘ tag ∗
        mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I.

Global Instance : LithiumUnfold (@zesuEncoderOptionalU64SomeCallSpec) := I.

Definition zesuEncoderOptionalU64NoneCallSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_c_call 32
    (fun args sp RET =>
      ∃ (value : bv 64) (tag : bv 8) (tail : spec),
      bv_unsigned (args !!! 0%nat) ↦ₘ value ∗
      (bv_unsigned (args !!! 0%nat) + 8) ↦ₘ tag ∗
      ⌜tag = BV 8 0⌝ ∗
      ⌜bv_extract 0 3 (args !!! 0%nat) = BV 3 0⌝ ∗
      ⌜0x20000000 <= bv_unsigned (args !!! 0%nat)⌝ ∗
      ⌜bv_unsigned (args !!! 0%nat) + 8 < 0x40000000⌝ ∗
      mmio_range 0x2401a0c0 16 ∗
      spec_trace
        (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1) tail) ∗
      RET (fun _ =>
        bv_unsigned (args !!! 0%nat) ↦ₘ value ∗
        (bv_unsigned (args !!! 0%nat) + 8) ↦ₘ tag ∗
        mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I.

Global Instance : LithiumUnfold (@zesuEncoderOptionalU64NoneCallSpec) := I.

Definition zesuEncoderOptionalU64CallSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesuEncoderOptionalU64SomeCallSpec ∨
   zesuEncoderOptionalU64NoneCallSpec)%I.

Global Instance : LithiumUnfold (@zesuEncoderOptionalU64CallSpec) := I.

Ltac unpack_zesu_encoder_optional_u64_call_spec call_spec :=
  lazymatch call_spec with
  | zesuEncoderOptionalU64SomeCallSpec =>
      iEval (unfold zesuEncoderOptionalU64SomeCallSpec, zesu_c_call)
        in "Hspec"
  | zesuEncoderOptionalU64NoneCallSpec =>
      iEval (unfold zesuEncoderOptionalU64NoneCallSpec, zesu_c_call)
        in "Hspec"
  end;
  iDestruct "Hspec" as (sp ret) "(Hsys & Htmp & Hrest)";
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest";
  iDestruct "Hrest" as (r10) "(R10 & Hrest)";
  iDestruct "Hrest" as (b10) "[%Hb10 Hrest]";
  iDestruct "Hrest" as (r11) "[R11 Hrest]";
  iDestruct "Hrest" as (b11) "[%Hb11 Hrest]";
  iDestruct "Hrest" as (r12) "[R12 Hrest]";
  iDestruct "Hrest" as (b12) "[%Hb12 Hrest]";
  iDestruct "Hrest" as (r13) "[R13 Hrest]";
  iDestruct "Hrest" as (b13) "[%Hb13 Hrest]";
  iDestruct "Hrest" as (r14) "[R14 Hrest]";
  iDestruct "Hrest" as (b14) "[%Hb14 Hrest]";
  iDestruct "Hrest" as (r15) "[R15 Hrest]";
  iDestruct "Hrest" as (b15) "[%Hb15 Hrest]";
  iDestruct "Hrest" as (r16) "[R16 Hrest]";
  iDestruct "Hrest" as (b16) "[%Hb16 Hrest]";
  iDestruct "Hrest" as (r17) "[R17 Hrest]";
  iDestruct "Hrest" as (b17) "[%Hb17 Hrest]";
  iDestruct "Hrest" as (r8) "(R8 & %Hr8 & Hrest)";
  iDestruct "Hrest" as (r9) "(R9 & %Hr9 & Hrest)";
  iDestruct "Hrest" as (r18) "(R18 & %Hr18 & Hrest)";
  iDestruct "Hrest" as (r19) "(R19 & %Hr19 & Hrest)";
  iDestruct "Hrest" as (r20) "(R20 & %Hr20 & Hrest)";
  iDestruct "Hrest" as (r21) "(R21 & %Hr21 & Hrest)";
  iDestruct "Hrest" as (r22) "(R22 & %Hr22 & Hrest)";
  iDestruct "Hrest" as (r23) "(R23 & %Hr23 & Hrest)";
  iDestruct "Hrest" as (r24) "(R24 & %Hr24 & Hrest)";
  iDestruct "Hrest" as (r25) "(R25 & %Hr25 & Hrest)";
  iDestruct "Hrest" as (r26) "(R26 & %Hr26 & Hrest)";
  iDestruct "Hrest" as (r27) "(R27 & %Hr27 & Hrest)";
  iDestruct "Hrest" as
    "(R1 & R2 & %Hspalign & %Hret0 & %Hret1 & %Hret2 &
      %Hstackbounds & Hstack & Hrest)";
  iDestruct "Hrest" as (value tag tail)
    "(Hvalue & Htagmem & %Htag & %Hdataalign & %Hdatamin &
      %Hdatamax & Hmmio & Htrace & Hret)";
  iEval (simpl) in "Hvalue";
  iEval (simpl) in "Htagmem";
  iEval (simpl) in "Hret".
