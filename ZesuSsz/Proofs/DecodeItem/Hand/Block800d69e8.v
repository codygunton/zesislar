Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.isla.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.

Definition DesignedEntry_800d69e8
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e8 (args) (frameBytes) (x13) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d69e8) := I.
Global Typeclasses Opaque DesignedEntry_800d69e8.

Local Ltac hand69e8_index :=
  first [lazymatch goal with
  | |- lithium.proof_state.SHELVED_SIDECOND (Z.of_nat _ = _) =>
    unfold lithium.proof_state.SHELVED_SIDECOND;
    lazymatch goal with |- ?P => let evidence := ZesuSsz.Automation.Hooks.zesu_registered_pure_fact P in exact evidence end
  end | lazymatch goal with
  | |- lithium.proof_state.SHELVED_SIDECOND _ => shelve
  | |- nat => shelve
  end].
Local Ltac hand69e8_step :=
  first [lazymatch goal with
  | |- envs_entails _ (wp_a_exp _ _) => liEnsureInvariant; try progress (unfold TRACE_LET);
    try liAIntroduceLetInGoal; liAExp; liSimpl
  end | zesu_liAStep].
Local Tactic Notation "hand69e8_recover" integer(count) := do count hand69e8_step.

Lemma DesignedBoundary_800d69e8 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte)  :
  instr_pre 0x800d698c (∃ (successor_locals : DecodeItemReturnLocals) (successor_pointerBytes : list byte) (successor_lengthBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_isLiteral : bool), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (successor_locals) (successor_pointerBytes) (successor_lengthBytes) (successor_inputPrefix) (successor_rest) (successor_isLiteral))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d69e8
    (DesignedEntry_800d69e8 args frameBytes x13 inputPrefix rest).
Proof.
iStartProof.
zesu_expose_code_lists.
repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
zesu_reduce_introduced_code_lists.
repeat iDestruct select (_ ∗ _)%I as "[? ?]".
1: hand69e8_recover 310.
Unshelve.
all: try hand69e8_index.
1: hand69e8_recover 250.
Unshelve.
all: try hand69e8_index.
1: hand69e8_recover 170.
Unshelve.
all: try hand69e8_index.
1: unfold TRACE.
1: hand69e8_recover 26.
1: unfold TRACE.
1: unfold IPM_JANNO.
1: iIntros "?".
1: zesu_liAStep.
1: hand69e8_recover 10.
1: intros (b7 & -> & Hmask).
1: unfold IPM_JANNO.
1: iIntros "?".
1: unfold LET_GOAL1, TRACE_LET, LET_ID; cbn beta.
1: hand69e8_recover 5.
1: unfold IPM_JANNO, LET_GOAL0, LET_ID; cbn beta.
1: hand69e8_recover 5.
1: unfold IPM_JANNO, LET_GOAL, LET_ID; cbn beta.
1: iSplit; [iPureIntro; f_equal; apply bool_decide_true; bv_solve | ].
1: unfold TRACE.
1: hand69e8_recover 6.
1: intros Hpc.
1: unfold IPM_JANNO.
1: iIntros "?".
1: unfold TRACE0.
1: hand69e8_recover 6.
1: assert (Hpcword : n6 = Z_to_bv 64 2148362748) by (apply bv_eq; exact (f_equal (fun v : base_val => match v with Val_Bits n => bvn_unsigned n | _ => 0 end) Hpc)).
1: subst n6.
1: hand69e8_recover 10.
1: unfold IPM_JANNO.
1: hand69e8_recover 5.
1: intros Halign.
1: unfold IPM_JANNO, TRACE0.
1: hand69e8_recover 3.
1: unfold TRACE0.
1: hand69e8_recover 3.
3: iPureIntro; exact I.
2: unfold IPM_JANNO, LET15, LET14, LET13; cbn; zesu_block.
1: hand69e8_recover 3.
1: assert (Hshort : bool_decide (bv_unsigned inputPrefix <= 127) = false) by (apply bool_decide_false; lia).
1: liExist; do 5 liExist.
1: liInst (fun x => x.1ₗ = false); liExInst.
1: liInst (fun x => x.3ₗ = bv_to_little_endian 8 8 (bv_unsigned x13)); liExInst.
1: liInst (fun x => x.3ₗ = bv_to_little_endian 8 8 (bv_unsigned LET5)); liExInst.
1: iMatchHyp ltac:(fun H P => lazymatch P with (decodeItemOutputPointer args ↦ₘ∗ ?storage)%I => liInst (fun x => x.3ₗ = {| returnA1 := LET5; returnA2 := LET0; returnA3 := x13; returnA4 := Z_to_bv 64 183; returnA5 := x15; returnA6 := x16; returnStorage := storage; returnFrame := frameBytes |}); liExInst end).
1: liInst (fun x => x.2ₗ = inputPrefix); liExInst.
1: liInst (fun x => x.1ₗ = rest); liExInst.
1: unfold decodeItemEntryAt800d698c, decodeItemReturnEntryCore; cbn [returnA1 returnA2 returnA3 returnA4 returnA5 returnA6 returnStorage returnFrame].
1: iFrame.
1: iExists tt.
1: unfold decodeItemBranchContinuation, decodeItemBranchContinuationAt; iFrame.
1: iSplit.
1: iPureIntro; repeat split; try assumption.
1: repeat first [progress rewrite length_drop | progress rewrite length_app | progress rewrite length_take | progress rewrite HarrayFact3 | progress cbn]; lia.
1: iPureIntro; repeat (first [assumption | split]).
1: apply (decodeItemRawInputSuccessor args inputPrefix rest); assumption.
1: change (RlpDecodeItem.littleEndian (bv_to_little_endian 8 8 (bv_unsigned x13)) = bv_unsigned inputPrefix - 128); rewrite decodeItemStoredWordValue; exact H3.
1: bv_solve.
all: try (first [apply decodeItemStoredPointerImage | apply decodeItemStoredLengthImage | apply decodeItemStoredWordBytes]).
all: rewrite skipn_skipn; let p := constr:(bv_to_little_endian 8 8 (bv_unsigned ((Z_to_bv 64 (decodeItemInputPointer args)) + 1)%bv)) in let l := constr:(bv_to_little_endian 8 8 (bv_unsigned x13)) in first [apply (decodeItemRawOutputStatus (decodeItemBeforeStorage args) p l) | apply (decodeItemRawOutputPad17 (decodeItemBeforeStorage args) p l) | apply (decodeItemRawOutputPad34 (decodeItemBeforeStorage args) p l)]; [exact HarrayFact3 | reflexivity | reflexivity].
Unshelve.
all: unfold lithium.proof_state.SHELVED_SIDECOND.
all: try reflexivity.
all: try (lazymatch goal with |- @eq valu _ _ => f_equal; f_equal; f_equal; apply bv_eq; reflexivity end).
all: try (f_equal; apply bool_decide_true; bv_solve).
all: repeat first [progress rewrite length_drop | progress rewrite length_app | progress rewrite length_take | progress rewrite HarrayFact3 | progress cbn]; lia.
Qed.
