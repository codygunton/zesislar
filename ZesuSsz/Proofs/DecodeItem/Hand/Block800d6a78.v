Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Common.
Require Import ZesuSsz.Compliance.DecodeItemShortListOutputMeaning.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import isla.isla.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
From iris.proofmode Require Import environments.

Definition DesignedEntry_800d6a78
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a78 (args) (locals) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a78) := I.
Global Typeclasses Opaque DesignedEntry_800d6a78.

Lemma DesignedBoundary_800d6a78 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte)  :
  decodeItemSelectedCode -∗
  instr_body 0x800d6a78
    (DesignedEntry_800d6a78 args locals inputPrefix rest).
Proof.
iStartProof.
zesu_expose_code_lists.
repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
zesu_reduce_introduced_code_lists.
repeat iDestruct select (_ ∗ _)%I as "[? ?]".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first (iPureIntro; reflexivity).
iExists 32%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; cbn [N.to_nat]; match goal with HstorageLength : length (returnStorage locals) = 40%nat |- _ => rewrite HstorageLength end; lia).
iIntros "HselectedOutput".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first done.
iExists 0%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; cbn [N.to_nat]; zesu_normalize_known_list_lengths; cbn [length]; zesu_normalize_known_list_lengths; lia).
iIntros "HselectedOutput".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first done.
iExists 8%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; cbn [N.to_nat]; zesu_normalize_known_list_lengths; cbn [length]; zesu_normalize_known_list_lengths; lia).
iIntros "HselectedOutput".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first (iPureIntro; rewrite Z.mod_1_r; reflexivity).
iExists 16%nat.
iSplitR; first (iPureIntro; rewrite Z.div_1_r; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; cbn [N.to_nat]; zesu_normalize_known_list_lengths; cbn [length]; zesu_normalize_known_list_lengths; lia).
iExists eq_refl.
iIntros "HselectedOutput".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first done.
iExists 24%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus in *; bv_solve).
iSplitR; first (iPureIntro; repeat progress (rewrite ?length_insert; cbn [N.to_nat length]; zesu_normalize_known_list_lengths); lia).
iIntros "HselectedOutput".
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => unify base ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)%Z); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first done.
iExists 8%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus, RlpDecodeItem.decodeItemStackBytes in *; bv_solve).
iSplitR; first (iPureIntro; zesu_integer_array_facts; cbn [N.to_nat]; lia).
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => unify base ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)%Z); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first done.
iExists 0%nat.
iSplitR; first (iPureIntro; unLET; zesu_integer_array_facts; unfold RlpDecodeItem.word64Modulus, RlpDecodeItem.decodeItemStackBytes in *; bv_solve).
iSplitR; first (iPureIntro; zesu_integer_array_facts; cbn [N.to_nat]; lia).
iIntros (savedFrameWord) "%HframeRead %HframeValue HretainedFrame".
subst savedFrameWord n13.
zesu_expose_environment_alias.
unfold LET29, TRACE.
pose proof (decodeItemSavedReturnDecoder args (returnFrame locals) H1) as HreturnDecoded; repeat match type of HreturnDecoded with context[Z.to_nat (?base + ?offset - ?base)] => replace (base + offset - base)%Z with offset in HreturnDecoded by lia end; cbn [N.to_nat Z.to_nat] in HreturnDecoded; rewrite HreturnDecoded.
pose proof (decodeItemSavedFramePointerDecoder args (returnFrame locals) H1) as HframeDecoded; repeat match type of HframeDecoded with context[Z.to_nat (?base + ?offset - ?base)] => replace (base + offset - base)%Z with offset in HframeDecoded by lia end; cbn [N.to_nat Z.to_nat] in HframeDecoded; rewrite HframeDecoded.
zesu_integer_array_facts.
match goal with Hselected : ((0 <= decodeItemReturnAddress args)%Z) |- _ => rename Hselected into HreturnLower end.
match goal with Hselected : ((decodeItemReturnAddress args < RlpDecodeItem.word64Modulus)%Z) |- _ => rename Hselected into HreturnUpper end.
match goal with Hselected : ((decodeItemReturnAddress args mod 4 = 0)%Z) |- _ => rename Hselected into HreturnAligned end.
match goal with Hselected : (length (returnFrame locals) = 16%nat) |- _ => rename Hselected into HretainedFrameLength end.
zesu_block.
iMatchHyp ltac:(fun H body => lazymatch body with | (decodeItemOutputPointer args ↦ₘ∗ ?image)%I => liInst (λ x, x.1ₗ = image) end).
zesu_block.
1: change (DecodeMeaningModuloKnownBugs args (decodeItemShortListUpdatedImage locals)); assert (HoutputFacts : decodeItemShortListOutputFacts args locals inputPrefix rest) by (unfold decodeItemShortListOutputFacts; repeat first [assumption | split]); ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts; assumption.
Unshelve.
all: zesu_finish.
Qed.
