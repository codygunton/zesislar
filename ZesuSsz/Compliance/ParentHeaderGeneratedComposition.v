(* decodeParentHeader compliance from its block obligations.
   The composition runs over the generated block table
   (ParentHeaderBlockObligations.v, from tools/block/render_open_blocks.py).
   A slot is closed by the block statement whose conclusion matches it: a
   compiled caller lemma (ParentHeaderClosedBlocks) or a premise field
   (ParentHeaderOpenBlocks). The theorem's premises are the open blocks and
   nextUint64's contract; the memcpy runtime premise is part of the contract
   code (memcpyCallPremise in parentHeaderContractCode). *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Automation2.BlockTable.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Contracts.NextUint64Contract.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.DecodeItemCallSpec2.
Require Import ZesuSsz.Contracts.NextUint64CallSpec2.
Require Import ZesuSsz.Compliance.DecodeItemCallSpec2.
Require Import ZesuSsz.Compliance.NextUint64CallSpec2.
Require Import ZesuSsz.Compliance.ParentHeaderCompositionBoundary.
Require Import ZesuSsz.Compliance.ParentHeaderBlockObligations.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0000Entries.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode nextUint64SelectedCode
  decodeItemSelectedCode.

(* ---- Infrastructure (no step names a block). ---- *)

Lemma parentHeader_body_weaken `{!islaG Sigma} `{!threadG} (a : Z) (P : iProp Sigma) :
  instr_body a (P ∗ True)%I -∗ instr_body a P.
Proof. iIntros "H". iApply (instr_pre_wand with "H"); [done|done|]. iIntros "$". Qed.

Lemma parentHeader_decodeItem_boxed `{!islaG Sigma} `{!threadG} :
  decodeItemSelectedCode -∗ □ instr_pre decodeItemEntry decodeItemCallSpec2.
Proof.
  iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply decodeItemCallSpec2_correct. iExact "Hcode".
Qed.

(* The membership of a slot: address and state both match, so several
   per-path slots may share one address. *)
Ltac parentHeader_member :=
  repeat lazymatch goal with
  | |- ?entry ∈ ?entry :: _ => apply elem_of_list_here
  | |- _ ∈ _ :: _ => apply elem_of_list_further
  end.

(* A premise is chosen by its address, never by trial unification: the callee
   specs share their machine_call shape, and unifying two of them unfolds both.
   The addresses are decodeItemEntry, nextUint64Entry and memcpyCsrPc (the
   notations carry a cast, which a pattern ignores with a warning). *)
Ltac parentHeader_premise :=
  lazymatch goal with
  | |- environments.envs_entails _ (instr_pre 0x800d6960 _) => iExact "Hdi"
  | |- environments.envs_entails _ (instr_pre 0x800d6274 _) => iExact "Hnu"
  | |- environments.envs_entails _ (instr_pre 0x800e06c0 _) => iExact "Hmc"
  | |- environments.envs_entails _ (instr_pre _ _) =>
      iApply (block_table_pre_lookup with "Htab");
      unfold parentHeaderBlockTable; cbn [block_table_entries];
      parentHeader_member
  | |- _ => iExact "Hsel"
  end.

(* The generic slot step: the block statement tagged with the slot's address
   and entry constant (slots of one block share the address; the entry tag
   selects syntactically, without trying another slot's statement). Its
   successor premises come from the table, its callee and code premises from
   the table code. *)
Ltac parentHeader_slot :=
  iIntros "#Htab";
  iPoseProof (block_table_pre_code with "Htab") as "#Hcode";
  iEval (unfold parentHeaderBlockTable; cbn [block_table_code];
         unfold parentHeaderTableCode, memcpyCallPremise) in "Hcode";
  iDestruct "Hcode" as "(Hsel & Hdi & Hnu & Hmc)";
  lazymatch goal with
  | |- environments.envs_entails _ (instr_body ?address (?entry _ _ _)) =>
      lazymatch goal with
      | H : parentHeaderBlockAt address entry _ |- _ =>
          let statement := fresh "Hstatement" in
          pose proof H as statement; unfold parentHeaderBlockAt in statement;
          iApply parentHeader_body_weaken; iApply statement; parentHeader_premise
      end
  end.

(* The block statements at one Sigma, from the closed record and the open premise. *)
Ltac parentHeader_block_statements Sigma Hopen :=
  pose proof parentHeaderClosedBlocks as Hclosed;
  destruct Hclosed; destruct Hopen;
  repeat match goal with
  | H : forall _ : gFunctors, _ |- _ => specialize (H Sigma _ _)
  end.

(* ---- Composition over the block table. ---- *)
Lemma parentHeader_entry_body `{!islaG Sigma} `{!threadG} :
  ParentHeaderOpenBlocks ->
  forall (args : ParentHeaderArgs) (returnAddress : Z),
  ⊢ □ parentHeaderTableCode -∗
    instr_body decodeParentHeaderEntry
      (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0000Entries.fp_machineAt0000 args returnAddress
        (parentHeaderContinuation args returnAddress)).
Proof.
  intros Hopen args returnAddress.
  parentHeader_block_statements Sigma Hopen.
  iIntros "#Htop".
  iApply (block_table_body (parentHeaderBlockTable args returnAddress)).
  { unfold parentHeaderBlockTable; cbn [block_table_entries]. parentHeader_member. }
  { iModIntro. iExact "Htop". }
  iModIntro. iIntros (address state Hin).
  unfold parentHeaderBlockTable in Hin; cbn [block_table_entries] in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]).
  all: try (apply elem_of_nil in Hin as []).
  all: injection Hin as Haddress Hstate; subst address state.
  all: parentHeader_slot.
Qed.

(* ---- Start bridge: the contract entry gives the generated entry state. ---- *)
Lemma parentHeader_start_bridge `{!islaG Sigma} `{!threadG}
    (args : ParentHeaderArgs) (returnAddress : Z) :
  (⌜bv_unsigned (parentHeaderReturnAddress args) = returnAddress⌝ ∗
   parentHeaderEntryResources args) ⊢
  ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0
    args returnAddress.
Proof.
  rewrite /parentHeaderEntryResources
    /ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0.
  iIntros "[%Hreturn (%x5 & %x6 & %x7 & %x13 & %x14 & %x15 & %x16 & %x17 & %x28 & %x29 & %x30 & %x31 & Hsys & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hinput & Hresult & Hframe & Hcallee & Hsource & Hnone & Hscratch & %Hwf & _)]".
  iExists x5, x6, x7, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  iExists (BV 64 0), (BV 64 0), (BV 64 0).
  assert (Hmod : bv_unsigned (parentHeaderReturnAddress args) mod 4 = 0)
    by (unfold parentHeaderArgsWellFormed in Hwf; tauto).
  iFrame. iPureIntro. split_and!;
    first [ assumption | exact I | vm_compute; reflexivity ].
Qed.

(* ---- The theorem: decodeParentHeader compliance, given the open blocks
   and nextUint64's contract. ---- *)
Theorem parentHeaderGeneratedCompliance :
  NextUint64ContractCorrect ->
  ParentHeaderOpenBlocks ->
  ParentHeaderContractCorrect.
Proof.
  intros Hnext Hopen returnAddress Sigma HG HT.
  change (⊢ (parentHeaderSelectedCode ∗ nextUint64SelectedCode ∗ decodeItemSelectedCode ∗
             □ instr_pre memcpyCsrPc memcpyCallSpec2) -∗ ∀ args : ParentHeaderArgs,
    instr_body decodeParentHeaderEntry
      ((⌜bv_unsigned (parentHeaderReturnAddress args) = returnAddress⌝ ∗
        parentHeaderEntryResources args) ∗
       parentHeaderContinuation args returnAddress))%I.
  iIntros "(#Hsel & #Hnu & #Hdi & #Hmc)" (args).
  iPoseProof (parentHeader_decodeItem_boxed with "Hdi") as "#Hdi2".
  iPoseProof (nextUint64CallSpec2_boxed Hnext with "Hnu") as "#Hnu2".
  iPoseProof (parentHeader_entry_body Hopen args returnAddress with "[]") as "Hbody".
  { iModIntro. unfold parentHeaderTableCode, memcpyCallPremise.
    iSplitR; [iExact "Hsel"|]. iSplitR; [iModIntro; iExact "Hdi2"|].
    iSplitR; [iModIntro; iExact "Hnu2"|]. iModIntro. iExact "Hmc". }
  iApply (instr_pre_wand with "Hbody"); [done|done|].
  iIntros "[Hentry Hcontinuation]".
  rewrite /ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0000Entries.fp_machineAt0000.
  iFrame "Hcontinuation".
  by iApply (parentHeader_start_bridge with "Hentry").
Qed.
