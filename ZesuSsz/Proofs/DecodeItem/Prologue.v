Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.WordArrayHandoff.
Require Import ZesuSsz.Automation.Switches.InstructionLookup.
Require Import ZesuSsz.Automation.Switches.StackWrite.
Require Import ZesuSsz.Automation.Switches.IntegerArrayAddress.
Require Import ZesuSsz.Automation.Switches.ArrayBounds.
Require Import ZesuSsz.Automation.Switches.RamFault.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
From Coq Require Import Lia.
From iris.proofmode Require Import environments.

Ltac decode_item_prologue_at_branch _ :=
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindInstrKind 0x800d6970 _) _) => idtac
  end.

Lemma decodeItemPrologueTo6974Bridge_correct : decodeItemPrologueTo6974Bridge.
Proof.
  unfold decodeItemPrologueTo6974Bridge.
  intros Sigma HG HT returnAddress args Hnonzero.
  iIntros "Hcode".
  iEval (unfold decodeItemSelectedCode) in "Hcode".
  iDestruct "Hcode" as "#Hcode".
  iStartProof.
  repeat first [progress iIntros (?) | progress iIntros "#?" |
    progress iIntros "?"].
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until decode_item_prologue_at_branch.
  all: try match goal with Hdomain : decodeItemDomainAt ?ret decodeItemC1BDomain ?arguments |- _ =>
    is_var ret; destruct Hdomain as [Hreturn Hdomain]; subst ret
  end.
  all: zesu_run.
  all: try solve [exfalso; apply Hnonzero;
    match goal with Hzero : _ = _ |- _ => rewrite Hzero; reflexivity end].
  all: try solve [lazymatch goal with
    | |- envs_entails _ _ => fail
    | _ => prepare_sidecond; first [reflexivity | assumption | lia |
        (unfold RlpDecodeItem.decodeItemStackBytes; bv_solve)]
    end].
  all: try match goal with Hdomain : decodeItemC1BDomain ?arguments |- _ =>
    pose proof (conj eq_refl Hdomain : decodeItemDomainAt (decodeItemReturnAddress arguments)
      decodeItemC1BDomain arguments) as HdomainAt;
    destruct (decodeItemDomainNonemptyInputHead (decodeItemReturnAddress arguments)
      arguments HdomainAt Hnonzero) as [inputPrefix [rest Hhead]] end.
  all: try match goal with Hframe : decodeItemSavedFrameFacts ?arguments ?frame |- _ =>
    iExists (li_pair a6 (li_pair a5 (li_pair a4 (li_pair a3
      (li_pair rest (li_pair inputPrefix (li_pair frame tt))))))); zesu_run end.
Unshelve.
all: prepare_sidecond.
all: try reflexivity.
all: try (unfold RlpDecodeItem.decodeItemStackBytes; lia).
all: try bv_solve.
Unshelve.
all: try (unfold RlpDecodeItem.decodeItemStackBytes;
  exact (zesu_Z_to_bv_add 64 (decodeItemStackPointer args) (-16))).
all: try solve [zesu_run].
Qed.

Print Assumptions decodeItemPrologueTo6974Bridge_correct.
