Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Compliance.DecodeItemMaskedReturnFacts.
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

Definition DesignedEntry_800d6ae0
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) : iProp Sigma :=
  ((ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (locals)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6ae0) := I.
Global Typeclasses Opaque DesignedEntry_800d6ae0.

Lemma DesignedBoundary_800d6ae0 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)  :
  decodeItemSelectedCode -∗
  instr_body 0x800d6ae0
    (DesignedEntry_800d6ae0 args locals).
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
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first (iPureIntro; reflexivity).
iExists 0%nat.
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first (iPureIntro; reflexivity).
iExists 8%nat.
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first (iPureIntro; reflexivity).
iExists 16%nat.
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first (iPureIntro; reflexivity).
iExists 24%nat.
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => unify base ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)%Z); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first (iPureIntro; reflexivity).
iExists 8%nat.
zesu_run_until ltac:(fun _ => lazymatch goal with |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac end).
zesu_expose_environment_alias.
iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => unify base ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)%Z); iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 8%N base values); cbn [mem_mapsto_kind_prop]; iFrameHyp name; cbn [N.eqb Pos.eqb] end).
iSplitR; first (iPureIntro; reflexivity).
iExists 0%nat.
zesu_integer_array_facts.
match goal with Hpin : ?T |- _ => let expected := constr:((length (returnFrame locals) = 16%nat)) in unify T expected; rename Hpin into HframeLength end.
match goal with Hpin : ?T |- _ => let expected := constr:((RlpDecodeItem.littleEndian (take 8%nat (drop 8%nat (returnFrame locals))) = decodeItemReturnAddress args)) in unify T expected; rename Hpin into HsavedReturnImage end.
match goal with Hpin : ?T |- _ => let expected := constr:((RlpDecodeItem.littleEndian (take 8%nat (drop 0%nat (returnFrame locals))) = bv_unsigned (decodeItemSavedFramePointer args))) in unify T expected; rename Hpin into HsavedFrameImage end.
match goal with Hpin : ?T |- _ => let expected := constr:((0 <= decodeItemReturnAddress args)%Z) in unify T expected; rename Hpin into HreturnNonnegative end.
match goal with Hpin : ?T |- _ => let expected := constr:((decodeItemReturnAddress args < RlpDecodeItem.word64Modulus)%Z) in unify T expected; rename Hpin into HreturnUpperBound end.
match goal with Hpin : ?T |- _ => let expected := constr:((decodeItemReturnAddress args mod 4 = 0)%Z) in unify T expected; rename Hpin into HreturnAddressAligned end.
assert (HreturnWord : Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop 8%nat (returnFrame locals)))) = Z_to_bv 64%N (decodeItemReturnAddress args)) by (rewrite <- decodeItemByteDecoderBridge; rewrite HsavedReturnImage; reflexivity).
assert (HreturnAligned : bv_extract 0%N 1%N (Z_to_bv 64%N (decodeItemReturnAddress args)) = BV 1%N 0%Z) by bv_solve.
rewrite /LET24 HreturnWord.
zesu_run_until ltac:(fun _ => lazymatch goal with |- iris.proofmode.environments.envs_entails _ (li_tactic (normalize_instr_addr ?a) _) => let address := eval cbv in a in tryif is_closed_term address then fail else idtac end).
1: unLET.
1: assert (HreturnAddZero : bv_add (Z_to_bv 64%N (decodeItemReturnAddress args)) (BV 64%N 0%Z) = Z_to_bv 64%N (decodeItemReturnAddress args)) by bv_solve.
1: (rewrite HreturnAddZero (decodeItemMaskedReturnAddress _ HreturnAligned) Z_to_bv_unsigned bv_wrap_small; last (unfold bv_modulus; change (0 <= decodeItemReturnAddress args < RlpDecodeItem.word64Modulus)%Z; lia)).
1: notypeclasses refine (tac_li_tactic _ _ (normalize_instr_addr_hint (decodeItemReturnAddress args) (decodeItemReturnAddress args) eq_refl) _ _).
1: cbn [li_tactic_P normalize_instr_addr_hint].
1: liFindInContext.
1: assert (HframeWord : Z_to_bv 64%N (little_endian_to_bv 8%N (take 8%nat (drop 0%nat (returnFrame locals)))) = decodeItemSavedFramePointer args) by (rewrite <- decodeItemByteDecoderBridge; rewrite HsavedFrameImage; apply Z_to_bv_bv_unsigned).
1: rewrite HframeWord (decodeItemStackEpilogueRestored args).
1: zesu_expose_environment_alias.
1: iMatchHyp ltac:(fun name resource => lazymatch resource with | (?base ↦ₘ∗ ?values)%I => constr_eq base (decodeItemOutputPointer args); iExists values end).
1: iSplitR.
1: (iPureIntro; split; first exact H0; lazymatch goal with |- DecodeMeaningModuloKnownBugs args ?after => assert (HerrorImage : after = RlpDecodeItemSchema.errorEncoding) by (generalize H2; generalize (returnStorage locals); intros before Hlength; do 40 (destruct before as [|? before]; [discriminate |]); destruct before; [unfold RlpDecodeItemSchema.errorEncoding; cbn [Z_to_bv N.to_nat take drop firstn skipn list_fmap fmap]; reflexivity | cbn in Hlength; lia]) end; rewrite HerrorImage; eapply decodeItemErrorPostMeaning; [exact (proj2 H0) | exact H3 | exact (proj1 errorReturnImage) | apply (proj2 errorReturnImage)]).
1: rewrite /decodeItemExitResources.
1: iFrame.
1: zesu_expose_environment_alias.
1: iRename select ((decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes) ↦ₘ∗ _)%I into "HframeBytes".
1: iDestruct (IslarisMemory.mem_mapsto_byte_array_to_mapsto_len 16 with "HframeBytes") as "Hframe"; first exact HframeLength.
1: (iSplitL "Hframe"; last done).
1: iApply (ghost_state.mem_mapsto_mapsto_to_uninit with "Hframe").
1: assert (HreturnSecondBit : bv_extract 0%N 1%N (bv_shiftr (bv_or (bv_and (bv_add (Z_to_bv 64%N (decodeItemReturnAddress args)) (BV 64%N 0%Z)) (BV 64%N 18446744073709551614%Z)) (BV 64%N 0%Z)) (BV 64%N 1%Z)) = BV 1%N 0%Z) by (clear -HreturnNonnegative HreturnUpperBound HreturnAddressAligned; unfold RlpDecodeItem.word64Modulus in *; bv_simplify_arith; assert (Hlow : bv_extract 0%N 1%N (Z_to_bv 64%N (decodeItemReturnAddress args)) = BV 1%N 0%Z) by bv_solve; pose proof (decodeItemMaskedReturnAddress (Z_to_bv 64%N (decodeItemReturnAddress args)) Hlow) as Hmask; bv_simplify_arith Hmask; rewrite Z.add_0_r Hmask (bv_wrap_small 64%N (decodeItemReturnAddress args)); last (change (0 <= decodeItemReturnAddress args < 2^64)%Z; lia); change ((decodeItemReturnAddress args / 2) mod 2 = 0)%Z; assert (Hmultiple : (decodeItemReturnAddress args = (decodeItemReturnAddress args / 4 * 2) * 2)%Z) by (pose proof (Z.div_mod (decodeItemReturnAddress args) 4%Z ltac:(lia)); lia); rewrite Hmultiple Z.div_mul; last lia; apply Z.mod_mul; lia).
1: (unLET; rewrite HreturnSecondBit in H36; discriminate).
Unshelve.
all: prepare_sidecond.
all: zesu_integer_array_facts.
all: zesu_finish.
all: unfold RlpDecodeItem.decodeItemStackBytes, RlpDecodeItem.word64Modulus in *; bv_solve.
Qed.
