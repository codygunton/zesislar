From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsCounterexample.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Open Scope Z_scope.

Lemma writeSuccessConcreteInitialStateRamBase args state :
  writeSuccessConcreteInitialState args state ->
  state.1.(seq_regs) !! "rv_ram_base" =
    Some (RVal_Bits (BV 64 0x20000000)).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsys & _).
  rewrite List.Forall_forall in Hsys.
  specialize (Hsys
    (KindReg "rv_ram_base",
      ExactShape (RVal_Bits (BV 64 0x20000000))) ltac:(cbn; tauto)).
  cbn in Hsys. destruct Hsys as (value & Hlookup & Hshape).
  subst value. exact Hlookup.
Qed.

Lemma Inv_15694_zero_remaining_has_zero_counter
    args sp pointer base total processed withdrawal allBytes prefix
    current suffix scratch encoderScratch registerFrame memoryFrame priorLog
    state :
  Inv_15694 args sp pointer base total processed 0 withdrawal
    allBytes prefix current suffix scratch encoderScratch registerFrame
    memoryFrame priorLog state ->
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 0)).
Proof. unfold Inv_15694. tauto. Qed.

Print Assumptions writeSuccessConcreteInitialStateRamBase.
Print Assumptions Inv_15694_zero_remaining_has_zero_counter.
