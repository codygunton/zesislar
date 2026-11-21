(* decodeParentHeader compliance from its block obligations.
   The composition runs over the generated block table
   (ParentHeaderBlockObligations.v, from tools/block/render_open_blocks.py).
   A slot is closed by the block statement whose conclusion matches it: a
   compiled caller lemma (ParentHeaderClosedBlocks) or a premise field
   (ParentHeaderOpenBlocks). The theorem's premises are the open blocks and the
   exit premises (ParentHeaderExitMeanings: the meaning of each exit package,
   step 2.4); nextUint64's correctness comes unconditionally from its generated
   interface (nextUint64CallSpec2_correct); the memcpy runtime premise is part of
   the contract code (memcpyCallPremise in parentHeaderContractCode). *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Automation2.BlockTable.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Interfaces.NextUint64.
Require Import ZesuSsz.Interfaces.DecodeItemCorrect.
Require Import ZesuSsz.Interfaces.NextUint64Correct.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderDomainRanges.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Compliance.ParentHeaderCompositionBoundary.
Require Import ZesuSsz.Compliance.ParentHeaderBlockObligations.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0000Entries.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.
Require Import ZesuSsz.Contracts.AbiBytes.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.
Require Import ZesuSsz.Compliance.ParentHeaderExitBridgeTactics.
Require Import ZesuSsz.Compliance.ParentHeaderTailExitBridge.
Require Import ZesuSsz.Compliance.ParentHeaderDirectExitBridgeSlot0.
Require Import ZesuSsz.Compliance.ParentHeaderDirectExitBridgeSlot1.
Require Import ZesuSsz.Compliance.ParentHeaderDirectExitBridgeSlot2.
Require Import ZesuSsz.Compliance.ParentHeaderDirectExitBridgeSlot3.
Require Import ZesuSsz.Compliance.ParentHeaderDirectExitBridgeSlot4.
Require Import ZesuSsz.Compliance.ParentHeaderDirectExitBridgeSlot5.
Require Import ZesuSsz.Compliance.ParentHeaderDirectExitBridgeSlot6.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent parentHeaderSelectedCode nextUint64SelectedCode
  decodeItemSelectedCode.

(* ---- Infrastructure (no step names a block). ---- *)

Lemma parentHeader_body_weaken `{!islaG Sigma} `{!threadG} (a : Z) (P : iProp Sigma) :
  instr_body a (P ∗ True)%I -∗ instr_body a P.
Proof. iIntros "H". iApply (instr_pre_wand with "H"); [done|done|]. iIntros "$". Qed.

(* An exit block (a slot of the return block 0x0274, the tail block 0x00b0)
   takes the return premise of its generated package from the K of its entry. *)
Lemma parentHeader_exit_slot `{!islaG Sigma} `{!threadG} (a : Z) (F Kc : iProp Sigma) :
  (Kc -∗ instr_body a ((F ∗ emp) ∗ True)%I) -∗ instr_body a (F ∗ Kc)%I.
Proof.
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "H [HF HK]". iApply ("H" with "HK"). by iFrame.
Qed.

Lemma parentHeader_decodeItem_boxed `{!islaG Sigma} `{!threadG} :
  decodeItemSelectedCode -∗ □ instr_pre decodeItemEntry decodeItemCallSpec2.
Proof.
  iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply decodeItemCallSpec2_correct. iExact "Hcode".
Qed.

(* nextUint64's contract code is its own map and decodeItem's map. *)
Lemma parentHeader_nextUint64_boxed `{!islaG Sigma} `{!threadG} :
  nextUint64SelectedCode ∗ decodeItemSelectedCode -∗
  □ instr_pre nextUint64Entry nextUint64CallSpec2.
Proof.
  iIntros "#[Hnu Hdi]". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply nextUint64CallSpec2_correct.
  rewrite /nextUint64ContractCode. iFrame "Hnu Hdi".
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
   notations carry a cast, which a pattern ignores with a warning). A return
   premise (its address is the variable returnAddress) is no table slot: the
   step fails at once instead of trying it against every table entry. *)
Ltac parentHeader_premise :=
  lazymatch goal with
  | |- environments.envs_entails _ (instr_pre 0x800d6960 _) => iExact "Hdi"
  | |- environments.envs_entails _ (instr_pre 0x800d6274 _) => iExact "Hnu"
  | |- environments.envs_entails _ (instr_pre 0x800e06c0 _) => iExact "Hmc"
  | |- environments.envs_entails _ (instr_pre ?a _) =>
      tryif is_var a then fail else
      solve [ iApply (block_table_pre_lookup with "Htab");
              unfold parentHeaderBlockTable; cbn [block_table_entries];
              parentHeader_member ]
  | |- _ => iExact "Hsel"
  end.


(* ---- Start bridge: the contract entry gives the generated entry state. ---- *)
(* The entry states the saved-register slots at the top of the frame as cells
   (offsets 320 to 392 from the frame base) and the rest of the frame as an
   uninitialized region; the contract gives one uninitialized region. *)
Lemma parentHeader_frame_cell `{!islaG Sigma} (sp kb : bv 64) (a n : Z) :
  400 <= bv_unsigned sp -> bv_unsigned kb < 400 ->
  a = bv_unsigned sp - 400 + bv_unsigned kb -> 8 <= n ->
  a ↦ₘ? n ⊢
  (∃ w : bv 64, bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551216)) kb) ↦ₘ w) ∗
  (a + 8) ↦ₘ? (n - 8).
Proof.
  intros Hsp Hk -> Hn. iIntros "H".
  iDestruct (mem_mapsto_uninit_split 8 with "H") as "[H $]"; [lia|].
  iDestruct (mem_mapsto_uninit_to_mapsto with "H") as (n' b) "[%Hn' H]".
  subst n'. iExists b.
  assert (Haddr : bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551216)) kb) =
                  bv_unsigned sp - 400 + bv_unsigned kb).
  { rewrite !bv_add_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l.
    change (bv_unsigned (BV 64 18446744073709551216)) with 18446744073709551216.
    change (bv_modulus 64) with (2 ^ 64).
    pose proof (bv_unsigned_in_range _ sp). pose proof (bv_unsigned_in_range _ kb).
    unfold bv_modulus in *. simpl in *.
    replace (bv_unsigned sp + 18446744073709551216 + bv_unsigned kb)
      with ((bv_unsigned sp - 400 + bv_unsigned kb) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  by rewrite Haddr.
Qed.

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
  pose proof (parentHeaderStackRange args Hwf) as Hsp.
  set (sp := parentHeaderStackPointer args) in *.
  iDestruct (mem_mapsto_uninit_split 320 with "Hframe") as "[Hlow Hcells]"; [lia|].
  iDestruct (parentHeader_frame_cell sp (BV 64 320) with "Hcells") as "[[%w320 Hc320] Hcells]";
    [lia|rewrite bv_unsigned_BV; lia|rewrite bv_unsigned_BV; lia|lia|].
  iDestruct (parentHeader_frame_cell sp (BV 64 328) with "Hcells") as "[[%w328 Hc328] Hcells]";
    [lia|rewrite bv_unsigned_BV; lia|rewrite bv_unsigned_BV; lia|lia|].
  iDestruct (parentHeader_frame_cell sp (BV 64 336) with "Hcells") as "[[%w336 Hc336] Hcells]";
    [lia|rewrite bv_unsigned_BV; lia|rewrite bv_unsigned_BV; lia|lia|].
  iDestruct (parentHeader_frame_cell sp (BV 64 344) with "Hcells") as "[[%w344 Hc344] Hcells]";
    [lia|rewrite bv_unsigned_BV; lia|rewrite bv_unsigned_BV; lia|lia|].
  iDestruct (parentHeader_frame_cell sp (BV 64 352) with "Hcells") as "[[%w352 Hc352] Hcells]";
    [lia|rewrite bv_unsigned_BV; lia|rewrite bv_unsigned_BV; lia|lia|].
  iDestruct (parentHeader_frame_cell sp (BV 64 360) with "Hcells") as "[[%w360 Hc360] Hcells]";
    [lia|rewrite bv_unsigned_BV; lia|rewrite bv_unsigned_BV; lia|lia|].
  iDestruct (parentHeader_frame_cell sp (BV 64 368) with "Hcells") as "[[%w368 Hc368] Hcells]";
    [lia|rewrite bv_unsigned_BV; lia|rewrite bv_unsigned_BV; lia|lia|].
  iDestruct (parentHeader_frame_cell sp (BV 64 376) with "Hcells") as "[[%w376 Hc376] Hcells]";
    [lia|rewrite bv_unsigned_BV; lia|rewrite bv_unsigned_BV; lia|lia|].
  iDestruct (parentHeader_frame_cell sp (BV 64 384) with "Hcells") as "[[%w384 Hc384] Hcells]";
    [lia|rewrite bv_unsigned_BV; lia|rewrite bv_unsigned_BV; lia|lia|].
  iDestruct (parentHeader_frame_cell sp (BV 64 392) with "Hcells") as "[[%w392 Hc392] _]";
    [lia|rewrite bv_unsigned_BV; lia|rewrite bv_unsigned_BV; lia|lia|].
  iExists x5, x6, x7, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  iExists w320, w328, w336, w344, w352, w360, w368, w376, w384, w392.
  assert (Hmod : bv_unsigned (parentHeaderReturnAddress args) mod 4 = 0)
    by (unfold parentHeaderArgsWellFormed in Hwf; tauto).
  iFrame. iPureIntro. split_and!;
    first [ assumption
          | apply zesu_hist_intro; exists (BV 64 0); split; vm_compute; reflexivity ].
Qed.

(* ---- End bridges (exit design A): each generated exit package (the memcpy
   tail package of 0x00b0, one return package per slot of 0x0274) gives the
   contract exit by its bridge (ParentHeaderTailExitBridge.v,
   ParentHeaderDirectExitBridgeSlot<k>.v); the meaning of each exit is an
   explicit premise (record ParentHeaderExitMeanings). ---- *)

(* The exit premises of the composition: the meaning of every exit package,
   step 2.4 (M1) discharges them. The direct ones are the generated
   exit-meaning declarations of the return packages at the contract meaning. *)
Record ParentHeaderExitMeanings : Prop := {
  parentHeaderExitMeaning_tail : parentHeaderTailExitMeaning;
  parentHeaderExitMeaning_slot0 :
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0_ExitMeaning
      parentHeaderResultMeaning;
  parentHeaderExitMeaning_slot1 :
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0_ExitMeaning
      parentHeaderResultMeaning;
  parentHeaderExitMeaning_slot2 :
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0_ExitMeaning
      parentHeaderResultMeaning;
  parentHeaderExitMeaning_slot3 :
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot3_ForwardA0N0_ExitMeaning
      parentHeaderResultMeaning;
  parentHeaderExitMeaning_slot4 :
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot4_ForwardA0N0_ExitMeaning
      parentHeaderResultMeaning;
  parentHeaderExitMeaning_slot5 :
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot5_ForwardA0N0_ExitMeaning
      parentHeaderResultMeaning;
  parentHeaderExitMeaning_slot6 :
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot6_ForwardA0N0_ExitMeaning
      parentHeaderResultMeaning
}.

(* The return premise of an exit package from the contract continuation K:
   the package's bridge gives the contract exit that K expects. *)
Ltac parentHeader_exit_premise Hexits H :=
  iEval (rewrite /parentHeaderContinuation) in H;
  iApply (instr_pre_wand with H); [done|done|];
  unfold ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.fp_machineReturnTail00e8,
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot0,
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot1,
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot2,
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot3,
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot4,
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot5,
    ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot6;
  iIntros "[Hexit _]";
  (* the bridge is chosen by the package's name: trying a wrong bridge
     unifies two packages, which unfolds both *)
  lazymatch iTypeOf (INamed "Hexit") with
  | Some (_, @ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.fp_machineReturnTail00e8_ForwardA0N0 _ _ _ _ _) =>
      iApply (parentHeader_tail_end_bridge with "Hexit"); exact (parentHeaderExitMeaning_tail Hexits)
  | Some (_, @ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 _ _ _ _ _) =>
      iApply (parentHeader_direct_end_bridge_slot0 with "Hexit"); exact (parentHeaderExitMeaning_slot0 Hexits)
  | Some (_, @ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 _ _ _ _ _) =>
      iApply (parentHeader_direct_end_bridge_slot1 with "Hexit"); exact (parentHeaderExitMeaning_slot1 Hexits)
  | Some (_, @ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 _ _ _ _ _) =>
      iApply (parentHeader_direct_end_bridge_slot2 with "Hexit"); exact (parentHeaderExitMeaning_slot2 Hexits)
  | Some (_, @ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot3_ForwardA0N0 _ _ _ _ _) =>
      iApply (parentHeader_direct_end_bridge_slot3 with "Hexit"); exact (parentHeaderExitMeaning_slot3 Hexits)
  | Some (_, @ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot4_ForwardA0N0 _ _ _ _ _) =>
      iApply (parentHeader_direct_end_bridge_slot4 with "Hexit"); exact (parentHeaderExitMeaning_slot4 Hexits)
  | Some (_, @ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot5_ForwardA0N0 _ _ _ _ _) =>
      iApply (parentHeader_direct_end_bridge_slot5 with "Hexit"); exact (parentHeaderExitMeaning_slot5 Hexits)
  | Some (_, @ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.fp_machineReturn_slot6_ForwardA0N0 _ _ _ _ _) =>
      iApply (parentHeader_direct_end_bridge_slot6 with "Hexit"); exact (parentHeaderExitMeaning_slot6 Hexits)
  end.

(* The generic slot step: the block statement tagged with the slot's address
   and entry constant (slots of one block share the address; the entry tag
   selects syntactically, without trying another slot's statement). Its
   successor premises come from the table, its callee and code premises from
   the table code. An exit block's return premise comes from K (its entry's
   continuation) through the exit package's bridge. *)
Ltac parentHeader_slot Hexits :=
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
          first
          [ iApply parentHeader_body_weaken; iApply statement; parentHeader_premise
          | iApply parentHeader_exit_slot; iIntros "Hret";
            iApply (statement with "[Hret]");
            [ parentHeader_exit_premise Hexits "Hret" | parentHeader_premise .. ] ]
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
  ParentHeaderOpenBlocks -> ParentHeaderExitMeanings ->
  forall (args : ParentHeaderArgs) (returnAddress : Z),
  ⊢ □ parentHeaderTableCode -∗
    instr_body decodeParentHeaderEntry
      (ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0000Entries.fp_machineAt0000 args returnAddress
        (parentHeaderContinuation args returnAddress)).
Proof.
  intros Hopen Hexits args returnAddress.
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
  all: parentHeader_slot Hexits.
Qed.

(* ---- The theorem: decodeParentHeader compliance, given the open blocks
   and the exit meanings. ---- *)
Theorem parentHeaderGeneratedCompliance :
  ParentHeaderOpenBlocks ->
  ParentHeaderExitMeanings ->
  ParentHeaderContractCorrect.
Proof.
  intros Hopen Hexits returnAddress Sigma HG HT.
  change (⊢ (parentHeaderSelectedCode ∗ nextUint64SelectedCode ∗ decodeItemSelectedCode ∗
             □ instr_pre memcpyCsrPc memcpyCallSpec2) -∗ ∀ args : ParentHeaderArgs,
    instr_body decodeParentHeaderEntry
      ((⌜bv_unsigned (parentHeaderReturnAddress args) = returnAddress⌝ ∗
        parentHeaderEntryResources args) ∗
       parentHeaderContinuation args returnAddress))%I.
  iIntros "(#Hsel & #Hnu & #Hdi & #Hmc)" (args).
  iPoseProof (parentHeader_decodeItem_boxed with "Hdi") as "#Hdi2".
  iPoseProof (parentHeader_nextUint64_boxed with "[$Hnu $Hdi]") as "#Hnu2".
  iPoseProof (parentHeader_entry_body Hopen Hexits args returnAddress with "[]") as "Hbody".
  { iModIntro. unfold parentHeaderTableCode, memcpyCallPremise.
    iSplitR; [iExact "Hsel"|]. iSplitR; [iModIntro; iExact "Hdi2"|].
    iSplitR; [iModIntro; iExact "Hnu2"|]. iModIntro. iExact "Hmc". }
  iApply (instr_pre_wand with "Hbody"); [done|done|].
  iIntros "[Hentry Hcontinuation]".
  rewrite /ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0000Entries.fp_machineAt0000.
  iFrame "Hcontinuation".
  by iApply (parentHeader_start_bridge with "Hentry").
Qed.
