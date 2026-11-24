(* entriesToOwnedSlice with a step bound (plan Stage T, T8), from the block
   obligations of the charged tree (EntriesToOwnedSliceBudgetBlockObligations.v).
   A copy of EntriesToOwnedSliceGeneratedComposition.v with the budget threaded: the
   start bridge is the uncharged one with the contract's step_budget framed
   into block 0x0000's entry; the return packages own no budget, so the end
   bridges are those of the uncharged composition (the charged packages are
   the same definitions); the table code is the charged code and the
   budgeted callee premises. Hand-written by the region owner. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Automation2.BlockTable.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.AltFlAllocBudgetPremises.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.ArrayListBudgetContract.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceContract.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBudgetContract.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceBlockEntries.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceChargedSelected.
Require Import ZesuSsz.Compliance.EntriesToOwnedSliceBudgetCompositionBoundary.
Require Import ZesuSsz.Compliance.EntriesToOwnedSliceBudgetBlockObligations.
Require Import ZesuSsz.Compliance.EntriesToOwnedSliceGeneratedComposition.
Require ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0000Entries.
Require ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.
Require ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0000Entries.
Require ZesuSsz.Generated.EntriesToOwnedSlice.FP301.FunctionReturnEntries.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent entriesToOwnedSliceChargedCode.

(* The charged entry of block 0x0000 is the uncharged one with the
   contract's step budget among its owned resources. *)
Lemma entriesToOwnedSliceBudget_entry_frame `{!islaG Sigma} `{!threadG}
    (args : EntriesToOwnedSliceBlockArgs) (returnAddress : Z) :
  (ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0 args returnAddress ∗
   step_budget entriesToOwnedSliceBudget) ⊢
  ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0 args returnAddress.
Proof.
  rewrite /ZesuSsz.Generated.EntriesToOwnedSlice.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0
    /ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0.
  iIntros "[H Hbudget]".
  repeat iDestruct "H" as (?) "H".
  repeat iExists _.
  iFrame.
Qed.

Lemma entriesToOwnedSliceBudget_start_bridge `{!islaG Sigma} `{!threadG}
    (args : ToOwnedSliceArgs) (returnAddress : Z) :
  (⌜bv_unsigned (toOwnedReturnAddress args) = returnAddress⌝ ∗
   toOwnedSliceEntry entriesElementBytes entriesLog2Alignment args ∗
   step_budget entriesToOwnedSliceBudget) ⊢
  ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0 (entriesBlockArgsOf args) returnAddress.
Proof.
  iIntros "(Hret & Hentry & Hbudget)".
  iApply entriesToOwnedSliceBudget_entry_frame. iFrame "Hbudget".
  iApply entriesToOwnedSlice_start_bridge. iFrame.
Qed.

(* ---- The return packages: the charged ones are the uncharged definitions. ---- *)

Section returns.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma entriesToOwnedSliceBudget_return_slot0 args returnAddress :
    ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 (Sigma:=Sigma) args returnAddress =
    ZesuSsz.Generated.EntriesToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 args returnAddress.
  Proof. reflexivity. Qed.

  Lemma entriesToOwnedSliceBudget_end_bridge_slot0 (args : ToOwnedSliceArgs) (returnAddress : Z) :
    ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 (entriesBlockArgsOf args) returnAddress ⊢
    entriesExit args returnAddress.
  Proof. rewrite entriesToOwnedSliceBudget_return_slot0. apply entries_end_bridge_slot0. Qed.

  Lemma entriesToOwnedSliceBudget_return_slot1 args returnAddress :
    ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 (Sigma:=Sigma) args returnAddress =
    ZesuSsz.Generated.EntriesToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 args returnAddress.
  Proof. reflexivity. Qed.

  Lemma entriesToOwnedSliceBudget_end_bridge_slot1 (args : ToOwnedSliceArgs) (returnAddress : Z) :
    ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 (entriesBlockArgsOf args) returnAddress ⊢
    entriesExit args returnAddress.
  Proof. rewrite entriesToOwnedSliceBudget_return_slot1. apply entries_end_bridge_slot1. Qed.

  Lemma entriesToOwnedSliceBudget_return_slot2 args returnAddress :
    ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 (Sigma:=Sigma) args returnAddress =
    ZesuSsz.Generated.EntriesToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 args returnAddress.
  Proof. reflexivity. Qed.

  Lemma entriesToOwnedSliceBudget_end_bridge_slot2 (args : ToOwnedSliceArgs) (returnAddress : Z) :
    ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 (entriesBlockArgsOf args) returnAddress ⊢
    entriesExit args returnAddress.
  Proof. rewrite entriesToOwnedSliceBudget_return_slot2. apply entries_end_bridge_slot2. Qed.
End returns.

(* ---- Composition over the block table. ---- *)

(* reg_col stays folded while the resources are framed. *)
#[local] Typeclasses Opaque reg_col.

(* A premise is chosen by its address: callee specs by their symbols, a
   successor by table lookup; a return premise (address returnAddress, a
   variable) is no table slot and fails at once. *)
Ltac budget_premise :=
  lazymatch goal with
  | |- environments.envs_entails _ (instr_pre ?a _) =>
      tryif is_var a then fail else
      tryif (let s := constr:(sym_alt_fl_alloc_alloc) in constr_eq a s) then iExact "Halloc" else
      tryif (let s := constr:(sym_alt_fl_alloc_remap) in constr_eq a s) then iExact "Hremap" else
      tryif (let s := constr:(sym_alt_fl_alloc_free) in constr_eq a s) then iExact "Hfree" else
      tryif (let s := constr:(sym_memcpy) in constr_eq a s) then iExact "Hmemcpy" else
      solve [ iApply (block_table_pre_lookup with "Htab");
              unfold entriesToOwnedSliceBudgetBlockTable; cbn [block_table_entries];
              entriesToOwnedSlice_member ]
  | |- _ => iExact "Hsel"
  end.

(* The return premise of a return package from the contract continuation:
   the end bridge of the package (chosen by its name) gives the contract exit. *)
Ltac budget_exit_premise H :=
  iEval (rewrite /entriesToOwnedSliceContinuation) in H;
  iApply (instr_pre_wand with H); [done|done|];
  unfold ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot0,
    ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot1,
    ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot2;
  iIntros "[Hexit _]";
  lazymatch iTypeOf (INamed "Hexit") with
  | Some (_, @ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 _ _ _ _ _) =>
      iApply (entriesToOwnedSliceBudget_end_bridge_slot0 with "Hexit")
  | Some (_, @ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 _ _ _ _ _) =>
      iApply (entriesToOwnedSliceBudget_end_bridge_slot1 with "Hexit")
  | Some (_, @ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 _ _ _ _ _) =>
      iApply (entriesToOwnedSliceBudget_end_bridge_slot2 with "Hexit")
  end.

Ltac budget_slot :=
  iIntros "#Htab";
  iPoseProof (block_table_pre_code with "Htab") as "#Hcode";
  iEval (unfold entriesToOwnedSliceBudgetBlockTable; cbn [block_table_code];
         unfold entriesToOwnedSliceBudgetTableCode) in "Hcode";
  iDestruct "Hcode" as "(Hsel & Halloc & Hremap & Hfree & Hmemcpy)";
  lazymatch goal with
  | |- environments.envs_entails _ (instr_body ?address (?entry _ _ _)) =>
      lazymatch goal with
      | H : entriesToOwnedSliceBudgetBlockAt address entry _ |- _ =>
          let statement := fresh "Hstatement" in
          pose proof H as statement; unfold entriesToOwnedSliceBudgetBlockAt in statement;
          first
          [ iApply entriesToOwnedSlice_body_weaken; iApply statement; budget_premise
          | iApply entriesToOwnedSlice_exit_slot; iIntros "Hret";
            iApply (statement with "[Hret]");
            [ budget_exit_premise "Hret" | budget_premise .. ] ]
      end
  end.

Ltac budget_block_statements Sigma Hopen :=
  pose proof entriesToOwnedSliceBudgetClosedBlocks as Hclosed;
  destruct Hclosed; destruct Hopen;
  repeat match goal with
  | H : forall _ : gFunctors, _ |- _ => specialize (H Sigma _ _)
  end.

Lemma entriesToOwnedSliceBudget_entry_body `{!islaG Sigma} `{!threadG} :
  EntriesToOwnedSliceBudgetOpenBlocks ->
  forall (args : ToOwnedSliceArgs) (returnAddress : Z),
  ⊢ □ entriesToOwnedSliceBudgetTableCode -∗
    instr_body sym_array_list_Aligned_input_AccessListEntry_null_toOwnedSlice
      (ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0000Entries.fp_machineAt0000 (entriesBlockArgsOf args) returnAddress
        (entriesToOwnedSliceContinuation (entriesBlockArgsOf args) returnAddress)).
Proof.
  intros Hopen args returnAddress.
  budget_block_statements Sigma Hopen.
  iIntros "#Htop".
  iApply (block_table_body (entriesToOwnedSliceBudgetBlockTable (entriesBlockArgsOf args) returnAddress)).
  { unfold entriesToOwnedSliceBudgetBlockTable; cbn [block_table_entries]. entriesToOwnedSlice_member. }
  { iModIntro. iExact "Htop". }
  iModIntro. iIntros (address state Hin).
  unfold entriesToOwnedSliceBudgetBlockTable in Hin; cbn [block_table_entries] in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]).
  all: try (apply elem_of_nil in Hin as []).
  all: injection Hin as Haddress Hstate; subst address state.
  all: budget_slot.
Qed.

(* ---- The theorem, from the open blocks. ---- *)
Theorem entriesToOwnedSliceBudgetComplianceFrom :
  EntriesToOwnedSliceBudgetOpenBlocks ->
  EntriesToOwnedSliceBudgetContractCorrect.
Proof.
  intros Hopen returnAddress Sigma HG HT.
  change (⊢ entriesToOwnedSliceBudgetContractCode -∗ ∀ args : ToOwnedSliceArgs,
    instr_body sym_array_list_Aligned_input_AccessListEntry_null_toOwnedSlice
      ((⌜bv_unsigned (toOwnedReturnAddress args) = returnAddress⌝ ∗
        toOwnedSliceEntry entriesElementBytes entriesLog2Alignment args ∗
        step_budget entriesToOwnedSliceBudget) ∗
       entriesToOwnedSliceContinuation (entriesBlockArgsOf args) returnAddress))%I.
  rewrite /entriesToOwnedSliceBudgetContractCode /altFlAllocatorBudgetPremises /altFlAllocBudgetCallPremise
    /altFlRemapBudgetCallPremise /altFlFreeBudgetCallPremise /ziskMemcpyBudgetCallPremise.
  iIntros "(#Hsel & (#Halloc & #Hremap & #Hfree) & #Hmemcpy)" (args).
  iPoseProof (entriesToOwnedSliceBudget_entry_body Hopen args returnAddress with "[]") as "Hbody".
  { iModIntro. unfold entriesToOwnedSliceBudgetTableCode. iFrame "#". }
  iApply (instr_pre_wand with "Hbody"); [done|done|].
  iIntros "[Hentry Hcontinuation]".
  rewrite /ZesuSsz.Generated.EntriesToOwnedSliceBudget.FP301.Pilot0000Entries.fp_machineAt0000.
  iFrame "Hcontinuation".
  by iApply (entriesToOwnedSliceBudget_start_bridge with "Hentry").
Qed.

(* Every block of the region is closed (EntriesToOwnedSliceBudgetOpenBlocks has no field). *)
Theorem entriesToOwnedSliceBudgetCompliance : EntriesToOwnedSliceBudgetContractCorrect.
Proof. exact (entriesToOwnedSliceBudgetComplianceFrom entriesToOwnedSliceBudgetOpenBlocks). Qed.
