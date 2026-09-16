Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsWithdrawalsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsMemcpy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsRest.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsMeasure.

Import ListNotations.
Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Record WriteSuccessWithdrawalsIterationState (Frame : Type) : Type := {
  writeSuccessIterationPc : Z;
  writeSuccessIterationPointer : Z;
  writeSuccessIterationProcessed : nat;
  writeSuccessIterationRemaining : nat;
  writeSuccessIterationSuffix : list (bv 8);
  writeSuccessIterationFrame : Frame
}.

Arguments writeSuccessIterationPc {Frame} _.
Arguments writeSuccessIterationPointer {Frame} _.
Arguments writeSuccessIterationProcessed {Frame} _.
Arguments writeSuccessIterationRemaining {Frame} _.
Arguments writeSuccessIterationSuffix {Frame} _.
Arguments writeSuccessIterationFrame {Frame} _.

Definition writeSuccessWithdrawalsIterationUpdate {Frame}
    (before after : WriteSuccessWithdrawalsIterationState Frame) : Prop :=
  writeSuccessIterationPc before = 0x15694 /\
  writeSuccessIterationRemaining before = S (writeSuccessIterationRemaining after) /\
  length (writeSuccessIterationSuffix before) =
    (48 * writeSuccessIterationRemaining before)%nat /\
  writeSuccessIterationPointer after = writeSuccessIterationPointer before + 48 /\
  writeSuccessIterationProcessed after = S (writeSuccessIterationProcessed before) /\
  writeSuccessIterationSuffix after = skipn 48 (writeSuccessIterationSuffix before) /\
  writeSuccessIterationFrame after = writeSuccessIterationFrame before /\
  writeSuccessIterationPc after =
    if writeSuccessIterationRemaining after is O then 0x156e8 else 0x15694.

Lemma writeSuccessWithdrawalsIterationDecreases {Frame}
    (before after : WriteSuccessWithdrawalsIterationState Frame) :
  writeSuccessWithdrawalsIterationUpdate before after ->
  (writeSuccessWithdrawalsMeasure (writeSuccessIterationSuffix after) <
   writeSuccessWithdrawalsMeasure (writeSuccessIterationSuffix before))%nat.
Proof.
  intros (_ & Hremaining & Hlength & _ & _ & Hsuffix & _ & _).
  rewrite Hsuffix. unfold writeSuccessWithdrawalsMeasure.
  rewrite skipn_length. rewrite Hlength. rewrite Hremaining. lia.
Qed.

Lemma writeSuccessWithdrawalsTotalShift processed remaining :
  (processed + S (S remaining))%nat = (S processed + S remaining)%nat.
Proof. lia. Qed.

Lemma writeSuccessWithdrawalsCounterDecrement remaining :
  (Z_to_bv 64 (S (S remaining)) +
    BV 64 18446744073709551615)%bv =
  Z_to_bv 64 (S remaining).
Proof.
  replace (BV 64 18446744073709551615) with (Z_to_bv 64 (-1)) by
    (apply bv_eq; vm_compute; reflexivity).
  rewrite Z_to_bv_add. f_equal. lia.
Qed.

Lemma writeSuccessWithdrawalsPointerAdvance pointer base processed :
  bv_unsigned pointer = (base + 48 * Z.of_nat processed)%Z ->
  (bv_unsigned pointer + 48 < 2 ^ 64)%Z ->
  bv_unsigned (pointer + BV 64 48)%bv =
    (base + 48 * Z.of_nat (S processed))%Z.
Proof.
  intros Hpointer Hrange.
  assert (Hsum :
      (bv_unsigned pointer + bv_unsigned (BV 64 48) < 2 ^ 64)%Z).
  { rewrite bv_unsigned_BV. cbn. exact Hrange. }
  pose proof (bv_unsigned_add_no_wrap_64 pointer (BV 64 48) Hsum) as Hadd.
  rewrite bv_unsigned_BV in Hadd. cbn in Hadd.
  rewrite Hadd Hpointer Nat2Z.inj_succ. lia.
Qed.

Definition writeSuccessWithdrawalsBeforeView
    (pointer : bv 64) (processed remaining : nat) (suffix : list (bv 8)) :
    WriteSuccessWithdrawalsIterationState unit := {|
  writeSuccessIterationPc := 0x15694;
  writeSuccessIterationPointer := bv_unsigned pointer;
  writeSuccessIterationProcessed := processed;
  writeSuccessIterationRemaining := S (S remaining);
  writeSuccessIterationSuffix := suffix;
  writeSuccessIterationFrame := tt
|}.

Definition writeSuccessWithdrawalsAfterView
    (pointer : bv 64) (processed remaining : nat) (suffix : list (bv 8)) :
    WriteSuccessWithdrawalsIterationState unit := {|
  writeSuccessIterationPc := 0x15694;
  writeSuccessIterationPointer := bv_unsigned (pointer + BV 64 48)%bv;
  writeSuccessIterationProcessed := S processed;
  writeSuccessIterationRemaining := S remaining;
  writeSuccessIterationSuffix := drop 48 suffix;
  writeSuccessIterationFrame := tt
|}.

Lemma writeSuccessWithdrawalsBackEdgeUpdate pointer processed remaining suffix :
  length suffix = (48 * S (S remaining))%nat ->
  bv_unsigned pointer <= (2 ^ 64 - 49)%Z ->
  writeSuccessWithdrawalsIterationUpdate
    (writeSuccessWithdrawalsBeforeView pointer processed remaining suffix)
    (writeSuccessWithdrawalsAfterView pointer processed remaining suffix).
Proof.
  intros Hlength Hpointer.
  unfold writeSuccessWithdrawalsIterationUpdate,
    writeSuccessWithdrawalsBeforeView, writeSuccessWithdrawalsAfterView.
  cbn. repeat split; try reflexivity.
  - exact Hlength.
  - apply bv_unsigned_add_no_wrap_64.
    rewrite bv_unsigned_BV. cbn. lia.
Qed.

Definition writeSuccessWithdrawalsBackEdgeSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes prefix suffix : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessWithdrawalsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits (pointer + BV 64 48)%bv ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
    base ↦ₘ∗ (prefix ++ take 48 suffix) ∗
    (bv_unsigned pointer + 48) ↦ₘ∗ drop 48 suffix ∗
    writeSuccessWithdrawalsScratch sp ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessWithdrawalsEvents sp (S remaining) tail) ∗ P ∗
    writeSuccessWithdrawalsInvariant sp (pointer + BV 64 48)%bv base total
      (S processed) remaining bytes (prefix ++ take 48 suffix)
      (drop 48 suffix) ∗
    instr_pre 0x156e8
      (writeSuccessWithdrawalsLoopExit sp base total bytes tail P) ∗
    ⌜writeSuccessWithdrawalsIterationUpdate
      (writeSuccessWithdrawalsBeforeView pointer processed remaining suffix)
      (writeSuccessWithdrawalsAfterView pointer processed remaining suffix)⌝ ∗
    True)%I.

Global Instance : LithiumUnfold (@writeSuccessWithdrawalsBackEdgeSpec) := I.

(** This is the same back-edge resource, with the strict suffix decrease
    derived from its concrete update. *)
Definition writeSuccessWithdrawalsDecreasingBackEdgeSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes prefix suffix : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessWithdrawalsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits (pointer + BV 64 48)%bv ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
    base ↦ₘ∗ (prefix ++ take 48 suffix) ∗
    (bv_unsigned pointer + 48) ↦ₘ∗ drop 48 suffix ∗
    writeSuccessWithdrawalsScratch sp ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessWithdrawalsEvents sp (S remaining) tail) ∗ P ∗
    writeSuccessWithdrawalsInvariant sp (pointer + BV 64 48)%bv base total
      (S processed) remaining bytes (prefix ++ take 48 suffix)
      (drop 48 suffix) ∗
    instr_pre 0x156e8
      (writeSuccessWithdrawalsLoopExit sp base total bytes tail P) ∗
    ⌜writeSuccessWithdrawalsIterationUpdate
      (writeSuccessWithdrawalsBeforeView pointer processed remaining suffix)
      (writeSuccessWithdrawalsAfterView pointer processed remaining suffix)⌝ ∗
    ⌜(ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsMeasure.writeSuccessWithdrawalsMeasure
         (writeSuccessIterationSuffix
           (writeSuccessWithdrawalsAfterView pointer processed remaining suffix)) <
       ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsMeasure.writeSuccessWithdrawalsMeasure
         (writeSuccessIterationSuffix
           (writeSuccessWithdrawalsBeforeView pointer processed remaining suffix)))%nat⌝ ∗
    True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessWithdrawalsDecreasingBackEdgeSpec) := I.

Lemma writeSuccessWithdrawalsBackEdgeSpecDecreases
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessWithdrawalsBackEdgeSpec P -∗
  writeSuccessWithdrawalsDecreasingBackEdgeSpec P.
Proof.
  rewrite /writeSuccessWithdrawalsBackEdgeSpec
    /writeSuccessWithdrawalsDecreasingBackEdgeSpec.
  iIntros "H".
  iDestruct "H" as
    (sp pointer base total processed remaining bytes prefix suffix tail)
    "(Hsys & Hregs & Hx2 & Hx8 & Hx9 & Hx18 & Hprefix & Hsuffix &
      Hscratch & Hmmio & Htrace & HP & Hinv & Hexit & %Hupdate & _)".
  iExists sp, pointer, base, total, processed, remaining, bytes, prefix,
    suffix, tail.
  iFrame. iSplit; first done.
  iSplit.
  - iPureIntro.
    exact (writeSuccessWithdrawalsIterationDecreases _ _ Hupdate).
  - done.
Qed.

Lemma write_success_withdrawals_tail_one_iteration
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15694 (writeSuccessWithdrawalsBackEdgeSpec P) -∗
  instr_body 0x156dc (writeSuccessWithdrawalsTailSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hback".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  do 101 liAStep.
  iRename select (base ↦ₘ∗ prefix)%I into "Hprefix".
  iRename select (bv_unsigned pointer ↦ₘ∗ suffix)%I into "Hsuffix".
  iDestruct (mem_mapsto_array_app 8%N (bv_unsigned pointer) (DfracOwn 1)
    (take 48 suffix) (drop 48 suffix) with "[Hsuffix]") as
    "[Hcurrent Hrest]".
  { rewrite take_drop. iExact "Hsuffix". }
  have Htake : length (take 48 suffix) = 48%nat.
  { rewrite length_take. lia. }
  have HpointerPrefix : bv_unsigned pointer =
      (base + Z.of_N (8 `div` 8) * length prefix)%Z.
  { cbn. rewrite H3 H1. nia. }
  iEval (rewrite HpointerPrefix) in "Hcurrent".
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    prefix (take 48 suffix) (length prefix) eq_refl
    with "Hprefix Hcurrent") as "Hprefix".
  iEval (rewrite Htake) in "Hrest".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  - have Hremaining : remaining = 0%nat.
    { bv_simplify_arith H13. bv_solve. }
    subst remaining.
    rewrite take_ge; [done | simpl in H2; lia].
  - have Hremaining : remaining = 0%nat.
    { bv_simplify_arith H13. bv_solve. }
    subst remaining. done.
  - have Hremaining : remaining = 0%nat.
    { bv_simplify_arith H13. bv_solve. }
    subst remaining.
    bv_simplify_arith. rewrite H3. bv_solve.
  - destruct remaining as [|remaining'].
    { exfalso. apply H13. bv_solve. }
    liARun.
    Unshelve.
    iExists
      (tail, suffix, prefix, prefix ++ suffix, remaining', processed,
       (processed + S (S remaining'))%nat, base, tt)ₗ.
    iFrame.
    repeat iSplit; try done.
    Unshelve.
    all: try prepare_sidecond.
    all: try assumption.
    all: try (cbn; rewrite ?length_take ?length_drop; lia).
    all: try rewrite ?take_drop ?app_assoc.
    all: try bv_solve.
    all: try nia.
    all: try iFrame.
    Unshelve.
    all: try prepare_sidecond.
    all: try assumption.
    all: try (cbn; rewrite ?length_take ?length_drop; lia).
    all: try rewrite ?take_drop ?app_assoc.
    all: try bv_solve.
    all: try nia.
    all: try iFrame.
    Unshelve.
    all: iPureIntro.
    all: first
      [ apply writeSuccessWithdrawalsTotalShift
      | unfold LET2; apply writeSuccessWithdrawalsCounterDecrement
      | rewrite <- app_assoc, take_drop; reflexivity
      | rewrite length_app H1 Htake; nia
      | rewrite length_drop H2; nia
      | apply writeSuccessWithdrawalsPointerAdvance; [exact H3 |];
        rewrite H3; nia
      | eapply Nat.lt_trans; [| exact H4]; lia
      | cbn; apply bv_unsigned_add_no_wrap_64;
        rewrite bv_unsigned_BV; cbn; rewrite H3; nia
      | match goal with |- ?G => idtac G; fail end ].
Qed.

Lemma write_success_withdrawals_one_iteration
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15694 (writeSuccessWithdrawalsBackEdgeSpec P) -∗
  instr_body 0x15694 (writeSuccessWithdrawalsLoopSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Hint #Houtput #Hback".
  iApply (write_success_withdrawals_memcpy P with
    "Hlookup Hcode Hmemcpy").
  iApply (write_success_withdrawals_rest P with
    "Hlookup Hcode Hint Houtput").
  iApply (write_success_withdrawals_tail_one_iteration P with
    "Hlookup Hcode Hback").
Qed.

Lemma write_success_withdrawals_one_iteration_decreases
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15694
    (writeSuccessWithdrawalsDecreasingBackEdgeSpec P) -∗
  instr_body 0x15694 (writeSuccessWithdrawalsLoopSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Hint #Houtput #Hdecreasing".
  iAssert (□ instr_pre 0x15694 (writeSuccessWithdrawalsBackEdgeSpec P))%I
    with "[]" as "#Hback".
  { iModIntro.
    iApply (instr_pre_wand 0x15694 0x15694 true true with "Hdecreasing");
      [done | done |].
    iApply writeSuccessWithdrawalsBackEdgeSpecDecreases. }
  iApply (write_success_withdrawals_one_iteration P with
    "Hlookup Hcode Hmemcpy Hint Houtput Hback").
Qed.

Print Assumptions writeSuccessWithdrawalsBackEdgeUpdate.
Print Assumptions writeSuccessWithdrawalsBackEdgeSpecDecreases.
Print Assumptions write_success_withdrawals_tail_one_iteration.
Print Assumptions write_success_withdrawals_one_iteration.
Print Assumptions write_success_withdrawals_one_iteration_decreases.
