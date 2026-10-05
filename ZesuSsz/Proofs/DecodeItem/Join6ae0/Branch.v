Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Switches.RecordWitness.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.InstructionLookup.
Require Import ZesuSsz.Automation.Switches.RamFault.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
From iris.proofmode Require Import environments.
Open Scope Z_scope.
Require Import ZesuSsz.Contracts.DecodeItemErrorBranch.

Ltac decode_item_error_at_return_witness _ :=
  first [match goal with
         | Hno : ~ ?P, Hyes : ?P |- _ => exfalso; exact (Hno Hyes)
         end
        | match goal with
          | Hge : ?a >= ?b, Hlt : ?a < ?b |- _ => exfalso; lia
          end
        | lazymatch goal with
          | |- envs_entails _ (@bi_exist _ ?T _) =>
      lazymatch T with
      | li_prod DecodeItemReturnLocals unit => idtac
      end
          end].

Ltac decode_item_error_at_trace_start _ :=
  lazymatch goal with
  | |- envs_entails _ (WPasm _) => idtac
  end.

Lemma decodeItemErrorBranchBridge_correct `{!islaG Sigma} `{!threadG}
    args (frameBytes : list byte) (masked : bv 64) :
  ⊢ decodeItemJoinTransferObligation 0x800d69e4 0x800d6ae0
    (decodeItemErrorBranchEntry args frameBytes masked)
    (decodeItemJoin6ae0Target args).
Proof.
  unfold decodeItemJoinTransferObligation, decodeItemErrorBranchEntry,
    decodeItemJoin6ae0Target.
  iIntros "Hcode".
  iEval (unfold decodeItemSelectedCode) in "Hcode".
  iDestruct "Hcode" as "#Hcode".
  zesu_run_until decode_item_error_at_trace_start.
  zesu_expose_environment_alias.
  assert (Hstorage : length (decodeItemBeforeStorage args) = 40%nat) by
    (match goal with Hdomain : decodeItemDomainAt _ _ args |- _ =>
       unfold decodeItemDomainAt, decodeItemC1BDomain,
         decodeItemArgsWellFormed in Hdomain; tauto
     end).
  match goal with Hguard : bv_unsigned masked >=
      bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) |- _ =>
    pose proof (decodeItemErrorUnsignedComparison masked
      (Z_to_bv 64 (decodeItemInputLength args)) Hguard) as Hsigned
  end.
  zesu_run_until decode_item_error_at_return_witness.
  all: try solve [exfalso; unLET; bv_solve].
Unshelve.
all: try solve [exfalso; unLET;
  match goal with Hbad : bv_extract _ _ _ = _ |- _ =>
    vm_compute in Hbad; discriminate
  end].
all: prepare_sidecond.
all: try solve [reflexivity | bv_solve].
Qed.

Print Assumptions decodeItemErrorBranchBridge_correct.
