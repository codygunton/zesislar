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

Definition DesignedEntry_800d6a38
    `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ((ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a38 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded) (inputPrefix) (rest)) ∗
   True)%I.
Global Instance : LithiumUnfold (@DesignedEntry_800d6a38) := I.
Global Typeclasses Opaque DesignedEntry_800d6a38.


Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Lemma DesignedBoundary_800d6a38 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte)   :
  instr_pre 0x800d6a40 (∃ (successor_locals : DecodeItemReturnLocals) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_headerLength : Z) (successor_payloadLength : Z), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a40 (args) (successor_locals) (successor_inputPrefix) (successor_rest) (successor_headerLength) (successor_payloadLength))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a38
    (DesignedEntry_800d6a38 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest).
Proof.
  iStartProof.
  zesu_expose_code_lists.
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
  zesu_reduce_introduced_code_lists.
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(zesu_liAStep)); run (Int.sub count 1)) else () in run 329).
  3: ltac2:(let rec run count := if Int.gt count 0 then (Control.focus 1 1 (fun () => ltac1:(zesu_liAStep)); run (Int.sub count 1)) else () in run 21).
  3: (match goal with
   | Hprovenance : decodeItemFoldProvenance args false inputPrefix rest n payloadStart lengthBytes |- _ =>
     destruct Hprovenance as (HinputHead & HprefixClass & Hwidth & Hstart & HlengthBytes)
   end;
   subst n payloadStart;
   iExists (decodeItemCompletedFoldLocals args (bv_unsigned inputPrefix - 183)
     (decodeItemInputPointer args + 1) lengthBytes frameBytes loaded),
     inputPrefix, rest, (1 + (bv_unsigned inputPrefix - 183)),
     (RlpDecodeItem.bigEndian lengthBytes)).
  3: (assert (Hprovenance : decodeItemFoldProvenance args false inputPrefix rest
         (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1) lengthBytes)
       by repeat first [assumption | reflexivity | split];
     zesu_block).
  1: (match goal with Hfault : ?bit = 1%bv |- _ => zesu_stack_closed_term bit; assert (HnoFault : bit <> 1%bv) by (vm_compute; discriminate); exfalso; exact (HnoFault Hfault) end).
  2: (match goal with Hfold : decodeItemByteFoldFacts _ ?width ?width _ ?bytes |- _ => assert (Htake : take (Z.to_nat width) bytes = bytes) by (apply firstn_all2; unfold decodeItemByteFoldFacts in Hfold; lia); rewrite Htake; reflexivity end).
  2: (match goal with Hfold : decodeItemByteFoldFacts ?args ?width ?width ?start ?bytes |- _ => symmetry; exact (decodeItemCompletedFoldConsumedWord args width start bytes Hfold) end).
  2: (assert (Hfits : decodeItemFoldLengthFits args (bv_unsigned inputPrefix - 183) lengthBytes = true) by (eapply decodeItemCompletedFoldFitsGuard; eassumption); match goal with Hdomain : decodeItemC1BDomain args, Hfold : decodeItemByteFoldFacts args _ _ _ lengthBytes |- _ => pose proof (decodeItemCompletedFoldAcceptedWitnessFacts args false inputPrefix rest (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1) lengthBytes Hdomain Hprovenance Hfold Hfits) as Haccepted; pose proof (decodeItemCompletedFoldWordValues args (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1) lengthBytes Hdomain Hfold) as (Hcursor & Hpayload & Hconsumed); pose proof (decodeItemCompletedFoldValueBounds args (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1) lengthBytes Hfold) as Hvalue; iPureIntro; repeat first [assumption | reflexivity | split | congruence | lia] end).
  2: (rewrite HlengthBytes; reflexivity). all: (iPureIntro; exact I).
  Unshelve. all: prepare_sidecond.
  all: try reflexivity. all: try (lazymatch goal with |- bv_and ?word 131072 = 0%bv => apply bv_eq; rewrite bv_and_unsigned; change (Z.land (bv_unsigned word) 131072 = 0); assumption end).
  3: (match goal with Hdomain : decodeItemC1BDomain ?actualArgs |- _ => pose proof Hdomain as Hfacts; destruct Hfacts as (_ & HstorageLength & _); destruct (decodeItemBeforeStorage actualArgs) as [|hd tl] eqn:Hstorage; simpl in HstorageLength; [lia | exists hd, tl; split; [reflexivity | lia]] end).
  all: (apply bv_eq; reflexivity).
Qed.
