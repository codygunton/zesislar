From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRegisterUpdate.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAfter.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyBoundaryFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyInduction.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Definition writeSuccessMemcpyLoopAfter regs global source destination bytes :=
  writeSuccessMemcpyBytesAfter (writeSuccess101d4Regs regs) global source
    destination (Z_to_bv 64 0) bytes.

Definition writeSuccessMemcpyEndpointGlobal regs global source destination bytes :=
  (writeSuccessMemcpyLoopAfter regs global source destination bytes).2.

Definition writeSuccessMemcpyEndpointRegs regs global source destination bytes
    returnAddress :=
  writeSuccess101dcRegs
    (writeSuccess101d8FallthroughRegs
      (writeSuccessMemcpyLoopAfter regs global source destination bytes).1.(seq_regs))
    returnAddress.

Lemma writeSuccessMemcpyEndpointLookupOther regs global source destination bytes
    returnAddress register :
  register <> "PC" ->
  register <> "x13" ->
  register <> "x14" ->
  register <> "x15" ->
  writeSuccessMemcpyEndpointRegs regs global source destination bytes
      returnAddress !! register = regs !! register.
Proof.
  intros Hpc Hx13 Hx14 Hx15.
  unfold writeSuccessMemcpyEndpointRegs.
  rewrite writeSuccess101dcRegsLookupOther; last exact Hpc.
  unfold writeSuccess101d8FallthroughRegs.
  rewrite lookup_insert_ne; last congruence.
  unfold writeSuccessMemcpyLoopAfter.
  rewrite writeSuccessMemcpyBytesAfterLookupOther;
    [|exact Hpc|exact Hx13|exact Hx14|exact Hx15].
  apply writeSuccess101d4RegsLookupOther; assumption.
Qed.

Lemma writeSuccessMemcpyFactsInsertPc regs (value : bv 64) :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (<["PC" := RVal_Bits value]> regs).
Proof.
  intros Hfacts. eapply writeSuccessOperationalRegisterFactsInsertBit.
  - exact Hfacts.
  - discriminate.
  - vm_compute. repeat constructor; discriminate.
  - left. reflexivity.
Qed.

Lemma writeSuccessMemcpyEndpointFacts regs global source destination bytes
    returnAddress :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessMemcpyEndpointRegs regs global source destination bytes
      returnAddress).
Proof.
  intros Hfacts.
  have Hinit : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccess101d4Regs regs).
  { apply writeSuccessMemcpyInitFacts. exact Hfacts. }
  have Hloop : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessMemcpyLoopAfter regs global source destination bytes).1.(seq_regs).
  { unfold writeSuccessMemcpyLoopAfter.
    apply writeSuccessMemcpyBytesAfterFacts. exact Hinit. }
  unfold writeSuccessMemcpyEndpointRegs, writeSuccess101dcRegs,
    writeSuccess101d8FallthroughRegs.
  apply writeSuccessMemcpyFactsInsertPc.
  apply writeSuccessMemcpyFactsInsertPc.
  exact Hloop.
Qed.

Lemma writeSuccessProtectedRegisterNotMemcpyClobber register :
  register ∈ writeSuccessWithdrawalsProtectedRegisters ->
  register <> "PC" /\ register <> "x13" /\ register <> "x14" /\
  register <> "x15".
Proof.
  unfold writeSuccessWithdrawalsProtectedRegisters.
  intros Hin. set_solver.
Qed.

Lemma writeSuccessMemcpyEndpointFrame regs global source destination bytes
    returnAddress frame :
  writeSuccessWithdrawalsRegisterFrame regs frame ->
  writeSuccessWithdrawalsRegisterFrame
    (writeSuccessMemcpyEndpointRegs regs global source destination bytes
      returnAddress) frame.
Proof.
  unfold writeSuccessWithdrawalsRegisterFrame.
  intros Hframe. apply Forall_forall. intros register Hin.
  destruct (writeSuccessProtectedRegisterNotMemcpyClobber register Hin) as
    (Hpc & Hx13 & Hx14 & Hx15).
  rewrite writeSuccessMemcpyEndpointLookupOther;
    [|exact Hpc|exact Hx13|exact Hx14|exact Hx15].
  apply (proj1 (Forall_forall _ _) Hframe). exact Hin.
Qed.

Lemma writeSuccessMemcpyEndpointInstrs regs global source destination bytes :
  (writeSuccessMemcpyEndpointGlobal regs global source destination bytes).(seq_instrs) =
    global.(seq_instrs).
Proof.
  unfold writeSuccessMemcpyEndpointGlobal, writeSuccessMemcpyLoopAfter.
  apply writeSuccessMemcpyBytesAfterInstrs.
Qed.

Lemma writeSuccessMemcpyEndpointExact regs global source destination bytes
    returnAddress returnTrace :
  bv_extract 0 2 returnAddress = BV 2 0 ->
  global.(seq_instrs) !! returnAddress = Some returnTrace ->
  writeSuccess101dcAfter
      (writeSuccess101d8FallthroughRegs
        (writeSuccessMemcpyLoopAfter regs global source destination bytes).1.(seq_regs))
      (writeSuccessMemcpyEndpointGlobal regs global source destination bytes)
      returnAddress =
    (writeSuccess15694Local returnTrace
       (writeSuccessMemcpyEndpointRegs regs global source destination bytes
         returnAddress),
     writeSuccessMemcpyEndpointGlobal regs global source destination bytes).
Proof.
  intros Halign Hlookup.
  have HfinalLookup :
      (writeSuccessMemcpyEndpointGlobal regs global source destination bytes).(seq_instrs)
        !! returnAddress = Some returnTrace.
  { rewrite writeSuccessMemcpyEndpointInstrs. exact Hlookup. }
  unfold writeSuccess101dcAfter, writeSuccessMemcpyEndpointRegs.
  rewrite (writeSuccessMemcpyReturnTargetExact returnAddress Halign).
  rewrite HfinalLookup. reflexivity.
Qed.

Print Assumptions writeSuccessMemcpyEndpointLookupOther.
Print Assumptions writeSuccessMemcpyEndpointFacts.
Print Assumptions writeSuccessMemcpyEndpointFrame.
Print Assumptions writeSuccessMemcpyEndpointInstrs.
Print Assumptions writeSuccessMemcpyEndpointExact.
