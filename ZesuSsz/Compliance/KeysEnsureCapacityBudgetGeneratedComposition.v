(* keysEnsureCapacity with a step bound (plan Stage T, T6), from the block
   obligations of the charged tree (KeysEnsureCapacityBudgetBlockObligations.v).
   A copy of KeysEnsureCapacityGeneratedComposition.v with the budget
   threaded: the start bridge hands the contract's step_budget to block
   0x0000's entry; the return packages own no budget, so the end bridges are
   those of the uncharged composition (the charged packages are the same
   definitions); the table code is the charged code and the budgeted callee
   premises. Hand-written by the region owner. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Automation2.BlockTable.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.AltFlAllocBudgetPremises.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityContract.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBudgetContract.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityChargedSelected.
Require Import ZesuSsz.Compliance.ArrayListBridges.
Require Import ZesuSsz.Compliance.KeysEnsureCapacityBudgetCompositionBoundary.
Require Import ZesuSsz.Compliance.KeysEnsureCapacityBudgetBlockObligations.
Require Import ZesuSsz.Compliance.KeysEnsureCapacityGeneratedComposition.
Require ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0000Entries.
Require ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.
Require ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacityChargedCode.

Lemma keysEnsureCapacityBudget_start_bridge `{!islaG Sigma} `{!threadG}
    (base : EnsureCapacityArgs) (returnAddress : Z) :
  (⌜bv_unsigned (ensureReturnAddress base) = returnAddress⌝ ∗ keysEnsureCapacityEntry base ∗
   step_budget keysEnsureCapacityBudget) ⊢
  ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0 {| ensureBase := base |} returnAddress.
Proof.
  rewrite /keysEnsureCapacityEntry /ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0.
  iIntros "(%Hret & (%x5 & %x6 & %x7 & %x13 & %x14 & %x15 & %x16 & %x17 & %x28 & %x29 & %x30 & %x31 & Hsys & H1 & H2 & H5 & H6 & H7 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H28 & H29 & H30 & H31 & Hsaved & Hhdr & Hbuf & Hscr & Halloc & Hvt & Hheap & Hframe & %Hd & _) & Hbudget)".
  iEval (rewrite arrayListSavedRegisters_unfold) in "Hsaved".
  iDestruct "Hsaved" as "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27)".
  iEval (rewrite arrayListBuffer_unfold) in "Hbuf". iDestruct "Hbuf" as "(Hitems & Htail & Hblock)".
  iEval (rewrite altFlAllocatorObject_unfold) in "Halloc".
  iEval (rewrite altFlVtable_unfold) in "Hvt".
  pose proof (keysEnsureCapacity_block_wellformed base Hd) as Hwf.
  pose proof (keysEnsureCapacity_stack_bound base Hd) as Hsp.
  iDestruct (ensure_frame_open with "Hframe") as "(Hcallee & Hscratch & %w88 & %w80 & %w72 & %w64 & %w56 & %w48 & %w40 & %w32 & %w24 & %w16 & %w8 & W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104)".
  iExists x5, x6, x7, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  iExists w88, w80, w72, w64, w56, w48, w40, w32, w24, w16, w8.
  unfold ensureBlockList; cbn [ensureBase].
  ensure_frame_addresses Hsp.
  iFrame.
  iPureIntro. split_and!.
  - split; [exact Hret|exact Hwf].
  - destruct Hd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hra). apply Z.mod_divide; [lia|exact Hra].
  - apply zesu_hist_intro. unfold ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0_Hist.
    exists (BV 64 0). split; vm_compute; reflexivity.
Qed.

(* ---- The return packages: the charged ones are the uncharged definitions. ---- *)

Section returns.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma keysEnsureCapacityBudget_return_slot0 args returnAddress :
    ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 (Sigma:=Sigma) args returnAddress =
    ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 args returnAddress.
  Proof. reflexivity. Qed.

  Lemma keysEnsureCapacityBudget_return_slot1 args returnAddress :
    ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 (Sigma:=Sigma) args returnAddress =
    ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 args returnAddress.
  Proof. reflexivity. Qed.

  Lemma keysEnsureCapacityBudget_return_slot2 args returnAddress :
    ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 (Sigma:=Sigma) args returnAddress =
    ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 args returnAddress.
  Proof. reflexivity. Qed.

  Lemma keysEnsureCapacityBudget_end_bridge_slot0 (base : EnsureCapacityArgs) (returnAddress : Z) :
    ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 {| ensureBase := base |} returnAddress ⊢
    keysEnsureCapacityPost base returnAddress.
  Proof. rewrite keysEnsureCapacityBudget_return_slot0. apply keysEnsureCapacity_end_bridge_slot0. Qed.

  Lemma keysEnsureCapacityBudget_end_bridge_slot1 (base : EnsureCapacityArgs) (returnAddress : Z) :
    ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 {| ensureBase := base |} returnAddress ⊢
    keysEnsureCapacityPost base returnAddress.
  Proof. rewrite keysEnsureCapacityBudget_return_slot1. apply keysEnsureCapacity_end_bridge_slot1. Qed.

  Lemma keysEnsureCapacityBudget_end_bridge_slot2 (base : EnsureCapacityArgs) (returnAddress : Z) :
    ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 {| ensureBase := base |} returnAddress ⊢
    keysEnsureCapacityPost base returnAddress.
  Proof. rewrite keysEnsureCapacityBudget_return_slot2. apply keysEnsureCapacity_end_bridge_slot2. Qed.
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
              unfold keysEnsureCapacityBudgetBlockTable; cbn [block_table_entries];
              ensure_member ]
  | |- _ => iExact "Hsel"
  end.

(* The return premise of a return package from the contract continuation:
   the end bridge of the package (chosen by its name) gives the contract exit. *)
Ltac budget_exit_premise H :=
  iEval (rewrite /keysEnsureCapacityContinuation) in H;
  iApply (instr_pre_wand with H); [done|done|];
  unfold ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot0,
    ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot1,
    ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot2;
  iIntros "[Hexit _]";
  lazymatch iTypeOf (INamed "Hexit") with
  | Some (_, @ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 _ _ _ _ _) =>
      iApply (keysEnsureCapacityBudget_end_bridge_slot0 with "Hexit")
  | Some (_, @ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 _ _ _ _ _) =>
      iApply (keysEnsureCapacityBudget_end_bridge_slot1 with "Hexit")
  | Some (_, @ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 _ _ _ _ _) =>
      iApply (keysEnsureCapacityBudget_end_bridge_slot2 with "Hexit")
  end.

Ltac budget_slot :=
  iIntros "#Htab";
  iPoseProof (block_table_pre_code with "Htab") as "#Hcode";
  iEval (unfold keysEnsureCapacityBudgetBlockTable; cbn [block_table_code];
         unfold keysEnsureCapacityBudgetTableCode) in "Hcode";
  iDestruct "Hcode" as "(Hsel & Halloc & Hremap & Hfree & Hmemcpy)";
  lazymatch goal with
  | |- environments.envs_entails _ (instr_body ?address (?entry _ _ _)) =>
      lazymatch goal with
      | H : keysEnsureCapacityBudgetBlockAt address entry _ |- _ =>
          let statement := fresh "Hstatement" in
          pose proof H as statement; unfold keysEnsureCapacityBudgetBlockAt in statement;
          first
          [ iApply ensure_body_weaken; iApply statement; budget_premise
          | iApply ensure_return_slot; iIntros "Hret";
            iApply (statement with "[Hret]");
            [ budget_exit_premise "Hret" | budget_premise .. ] ]
      end
  end.

Ltac budget_block_statements Sigma Hopen :=
  pose proof keysEnsureCapacityBudgetClosedBlocks as Hclosed;
  destruct Hclosed; destruct Hopen;
  repeat match goal with
  | H : forall _ : gFunctors, _ |- _ => specialize (H Sigma _ _)
  end.

Lemma keysEnsureCapacityBudget_entry_body `{!islaG Sigma} `{!threadG} :
  KeysEnsureCapacityBudgetOpenBlocks ->
  forall (base : EnsureCapacityArgs) (returnAddress : Z),
  ⊢ □ keysEnsureCapacityBudgetTableCode -∗
    instr_body sym_array_list_Aligned_32_u8_null_ensureTotalCapacity
      (ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0000Entries.fp_machineAt0000 {| ensureBase := base |} returnAddress
        (keysEnsureCapacityContinuation {| ensureBase := base |} returnAddress)).
Proof.
  intros Hopen base returnAddress.
  budget_block_statements Sigma Hopen.
  iIntros "#Htop".
  iApply (block_table_body (keysEnsureCapacityBudgetBlockTable {| ensureBase := base |} returnAddress)).
  { unfold keysEnsureCapacityBudgetBlockTable; cbn [block_table_entries]. ensure_member. }
  { iModIntro. iExact "Htop". }
  iModIntro. iIntros (address state Hin).
  unfold keysEnsureCapacityBudgetBlockTable in Hin; cbn [block_table_entries] in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]).
  all: try (apply elem_of_nil in Hin as []).
  all: injection Hin as Haddress Hstate; subst address state.
  all: budget_slot.
Qed.

(* ---- The theorem, from the open blocks. ---- *)
Theorem keysEnsureCapacityBudgetComplianceFrom :
  KeysEnsureCapacityBudgetOpenBlocks ->
  KeysEnsureCapacityBudgetContractCorrect.
Proof.
  intros Hopen returnAddress Sigma HG HT.
  change (⊢ keysEnsureCapacityBudgetContractCode -∗ ∀ base : EnsureCapacityArgs,
    instr_body sym_array_list_Aligned_32_u8_null_ensureTotalCapacity
      ((⌜bv_unsigned (ensureReturnAddress base) = returnAddress⌝ ∗ keysEnsureCapacityEntry base ∗
        step_budget keysEnsureCapacityBudget) ∗
       instr_pre returnAddress (keysEnsureCapacityPost base returnAddress)))%I.
  iIntros "Hcode" (base).
  rewrite /keysEnsureCapacityBudgetContractCode /altFlAllocatorBudgetPremises /altFlAllocBudgetCallPremise
    /altFlRemapBudgetCallPremise /altFlFreeBudgetCallPremise /ziskMemcpyBudgetCallPremise.
  iDestruct "Hcode" as "(#Hsel & (#Halloc & #Hremap & #Hfree) & #Hmemcpy)".
  iPoseProof (keysEnsureCapacityBudget_entry_body Hopen base returnAddress with "[]") as "Hbody".
  { iModIntro. unfold keysEnsureCapacityBudgetTableCode. iFrame "#". }
  iApply (instr_pre_wand with "Hbody"); [done|done|].
  iIntros "[Hentry Hexit]".
  rewrite /ZesuSsz.Generated.KeysEnsureCapacityBudget.FP301.Pilot0000Entries.fp_machineAt0000 /keysEnsureCapacityContinuation.
  iSplitL "Hentry"; [by iApply keysEnsureCapacityBudget_start_bridge|].
  iExact "Hexit".
Qed.

(* Every block of the region is closed (KeysEnsureCapacityBudgetOpenBlocks has no field). *)
Theorem keysEnsureCapacityBudgetCompliance : KeysEnsureCapacityBudgetContractCorrect.
Proof. exact (keysEnsureCapacityBudgetComplianceFrom keysEnsureCapacityBudgetOpenBlocks). Qed.
