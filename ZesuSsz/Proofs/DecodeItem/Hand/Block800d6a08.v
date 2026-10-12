Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import SailStdpp.MachineWord.
From iris.proofmode Require Import environments.

Definition DesignedEntry_800d6a08
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a08 (args) (frameBytes) (x13) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a08) := I.
Global Typeclasses Opaque DesignedEntry_800d6a08.


Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Local Tactic Notation "hand6a08_recover" integer(count) :=
  do count (ltac2:(Control.focus 1 1 (fun () => ltac1:(zesu_liAStep)))).

Lemma DesignedBoundary_800d6a08 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte)   :
  instr_pre 0x800d6a14 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_oldAcc : bv 64) (successor_oldCursor : bv 64) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a14 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_oldAcc) (successor_oldCursor) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a08
    (DesignedEntry_800d6a08 args frameBytes x13 inputPrefix rest).
Proof.
iStartProof.
zesu_expose_code_lists.
repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
zesu_reduce_introduced_code_lists.
repeat iDestruct select (_ ∗ _)%I as "[? ?]".
1: do 10 zesu_liAStep.
1: hand6a08_recover 100.
1: hand6a08_recover 100.
1: hand6a08_recover 100.
1: hand6a08_recover 60.
1: assert (Hmask : bv_unsigned LET2 = bv_unsigned inputPrefix - 183) by (unfold LET2, LET0; pose proof (zesu_unsigned_low_mask_add_integer 64 8 x13 255 73 ltac:(done) ltac:(reflexivity)) as Hlow; rewrite Hlow H3 Z_to_bv_unsigned; change ((bv_unsigned inputPrefix + 73) mod 256 = bv_unsigned inputPrefix - 183); replace (bv_unsigned inputPrefix + 73) with ((bv_unsigned inputPrefix - 183) + 1 * 256) by ring; rewrite Z.mod_add; [apply Z.mod_small; lia | lia]).
1: pose proof (ZesuSsz.Compliance.DecodeItemSemanticIntroduction.decodeItemDomainInputLengthBounds args (proj2 H6)) as Hlength.
1: assert (Hlen : 0 <= decodeItemInputLength args < bv_modulus 64) by (unfold bv_modulus; simpl; lia).
1: rewrite !zesu_signed_zero_extend_64_128 Hmask (Z_to_bv_small 64 _ Hlen) in H10.
1: assert (Hrejected : decodeItemRejectedFacts args).
1: eapply (ZesuSsz.Compliance.DecodeItemSailIntroduction.decodeItemLongStringHeaderRejected args inputPrefix rest).
1: exact (proj2 H6).
1: exact H0.
1: split; assumption.
1: destruct (proj2 H6) as (Hinput & Hstorage & Hlayout).
1: rewrite -Hinput.
1: rewrite Z.add_1_l; apply (proj2 (Z.lt_succ_r _ _)); exact (Z.ge_le _ _ H10).
1: zesu_block.
1: unfold LET7, LET6, LET5; zesu_block.
1: hand6a08_recover 10.
1: hand6a08_recover 20.
1: assert (Hwidth : 1 <= bv_unsigned inputPrefix - 183 <= 8) by lia.
1: pose proof (decodeItemStringHeaderReadGuardFacts args x13 inputPrefix H6 (conj H1 H2) H3 H10) as Hfits.
1: pose proof (decodeItemStringHeaderProvenanceFacts args inputPrefix rest H0 (conj H1 H2)) as Hprovenance.
1: pose proof (decodeItemHeaderInitialFoldFacts (decodeItemReturnAddress args) args inputPrefix rest (bv_unsigned inputPrefix - 183) H6 H0 Hwidth Hfits) as Hfold.
1: lazymatch goal with |- context[decodeItemByteFoldFacts args ?width 0 ?start ?bytes] => unify width (bv_unsigned inputPrefix - 183); unify start (decodeItemInputPointer args + 1); unify bytes (firstn (Z.to_nat (bv_unsigned inputPrefix - 183)) rest) end.
1: zesu_block.
all: try (iPureIntro; exact I).
1: apply bv_eq; rewrite (zesu_unsigned_low_mask_add_integer 64 8 x13 255 73 ltac:(done) ltac:(reflexivity)) H3 (Z_to_bv_small 64 (bv_unsigned inputPrefix - 183) ltac:(unfold bv_modulus; simpl; lia)); change ((bv_unsigned inputPrefix + 73) mod 256 = bv_unsigned inputPrefix - 183); replace (bv_unsigned inputPrefix + 73) with ((bv_unsigned inputPrefix - 183) + 1 * 256) by ring; rewrite Z.mod_add; [apply Z.mod_small; lia | lia].
Unshelve.
all: prepare_sidecond.
all: try reflexivity.
all: try solve [apply bv_eq; rewrite bv_and_unsigned; change (Z.land _ 131072 = 0); assumption].
all: try solve [reflexivity | exact (proj2 H6)].
1: pose proof (ZesuSsz.Compliance.DecodeItemSemanticIntroduction.decodeItemDomainInputLengthBounds args (proj2 H6)) as Hlength.
6: pose proof (ZesuSsz.Compliance.DecodeItemSemanticIntroduction.decodeItemDomainInputLengthBounds args (proj2 H6)) as Hlength.
6: assert (Hlen : 0 <= decodeItemInputLength args < bv_modulus 64) by (unfold bv_modulus; simpl; lia).
6: rewrite (Z_to_bv_small 64 _ Hlen).
6: exact (decodeItemStringHeaderReadGuardFacts args x13 inputPrefix H6 (conj H1 H2) H3 H10).
1: apply bv_eq; rewrite bv_and_unsigned; change (Z.land (bv_unsigned b) 131072 = 0); exact H7.
1: apply bv_eq; rewrite bv_and_unsigned; change (Z.land (bv_unsigned b0) 131072 = 0); exact H8.
1: apply bv_eq; lazymatch goal with |- ?left = ?right => zesu_stack_closed_term left; zesu_stack_closed_term right end; vm_compute; reflexivity.
1: apply bv_eq; lazymatch goal with |- ?left = ?right => zesu_stack_closed_term left; zesu_stack_closed_term right end; vm_compute; reflexivity.
1: apply bv_eq; rewrite bv_and_unsigned; change (Z.land (bv_unsigned b1) 131072 = 0); exact H9.
Qed.
