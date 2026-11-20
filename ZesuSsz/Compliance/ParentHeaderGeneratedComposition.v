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

Lemma parentHeader_nextUint64_boxed `{!islaG Sigma} `{!threadG} :
  NextUint64ContractCorrect ->
  nextUint64SelectedCode -∗ □ instr_pre nextUint64Entry nextUint64CallSpec2.
Proof.
  intros Hcontract. iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply (nextUint64CallSpec2_correct Hcontract). iExact "Hcode".
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

(* ---- End bridge (exit design A, DRAFT): the generated machine exit gives the
   contract exit. The bridge chooses the outcome, reshapes the registers and
   folds the frame; the meaning is an explicit premise in the form of plan
   step 2.4 (M1): the exit's history implies the meaning of its result. ---- *)

(* The meaning premise of the memcpy tail exit. *)
Definition parentHeaderTailExitMeaning : Prop :=
  forall (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome),
    bv_unsigned (parentHeaderReturnAddress args) = returnAddress ->
    parentHeaderArgsWellFormed args ->
    zesu_hist (ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.fp_machineReturnTail00e8_ForwardA0N0_Hist
      args returnAddress call_after) ->
    ParentHeaderMeaningModuloKnownBugs (parentHeaderCall args) (parentHeaderMemcpySourceBefore args).

Lemma parentHeader_frame_address (sp kb : bv 64) :
  400 <= bv_unsigned sp -> bv_unsigned kb < 400 ->
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551216)) kb) = bv_unsigned sp - 400 + bv_unsigned kb.
Proof.
  intros Hsp Hk. rewrite !bv_add_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l.
  change (bv_unsigned (BV 64 18446744073709551216)) with 18446744073709551216.
  change (bv_modulus 64) with (2 ^ 64).
  pose proof (bv_unsigned_in_range _ sp). pose proof (bv_unsigned_in_range _ kb).
  unfold bv_modulus in *. simpl in *.
  replace (bv_unsigned sp + 18446744073709551216 + bv_unsigned kb)
    with ((bv_unsigned sp - 400 + bv_unsigned kb) + 1 * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* A saved-register cell of the frame as its eight bytes at the frame offset. *)
Lemma parentHeader_cell_bytes `{!islaG Sigma} (sp kb w : bv 64) :
  400 <= bv_unsigned sp -> bv_unsigned kb < 400 ->
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551216)) kb) ↦ₘ w ⊢
  (bv_unsigned sp - 400 + bv_unsigned kb) ↦ₘ∗ bv_to_little_endian 8 8 (bv_unsigned w) ∗
  ⌜Z.of_nat (length (bv_to_little_endian 8 8 (bv_unsigned w))) = 8⌝.
Proof.
  intros Hsp Hk. rewrite parentHeader_frame_address //. iIntros "H".
  iApply (zesu_cell_bytes 8 with "H").
Qed.

(* Joins the next frame piece onto the run "R" of n bytes. *)
Ltac parentHeader_join spec n m :=
  iDestruct (zesu_byte_array_join_sized _ _ _ _ _ n m (n + m) with spec) as "R";
  [lia|lia|rewrite ?bv_unsigned_BV; lia|reflexivity|].

Lemma parentHeader_tail_end_bridge `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) :
  parentHeaderTailExitMeaning ->
  ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.fp_machineReturnTail00e8_ForwardA0N0
    args returnAddress ⊢
  ∃ outcome : ParentHeaderOutcome,
    ⌜bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\
     parentHeaderAllows (parentHeaderCall args) outcome⌝ ∗
    parentHeaderExitResources args outcome.
Proof.
  intros Hmeaning.
  rewrite /ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnTail00e8Entries.fp_machineReturnTail00e8_ForwardA0N0.
  iIntros "(%x1 & %x5 & %x6 & %x7 & %x10 & %x11 & %x12 & %x13 & %x14 & %x15 & %x16 & %x17 & %x28 & %x29 & %x30 & %x31 & %after & Hsys & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hin & Hres & F0 & F8 & F48 & C320 & C328 & C336 & C344 & C352 & C360 & C368 & C376 & C384 & C392 & Hcallee & Hsrc & Hnone & Hscr & %Hra & %Hmod & %Hlen & %Hlen80 & %Hlen8 & %Hcall & %Hhist)".
  destruct Hra as [Hret Hwf].
  pose proof (parentHeaderStackRange args Hwf) as Hsp.
  (* The frame: every piece as bytes, joined into the contract's 400-byte array. *)
  iDestruct (zesu_uninit_bytes _ 8 8 with "F0") as (l0) "[%H0 R]"; [done|].
  iDestruct (zesu_uninit_bytes _ 272 272 with "F48") as (l48) "[%H48 F48]"; [done|].
  assert (H8b : Z.of_nat (length after) = 40) by lia.
  iDestruct (parentHeader_cell_bytes _ (BV 64 320) with "C320") as "[C320 %K320]"; [lia|rewrite bv_unsigned_BV; lia|].
  iDestruct (parentHeader_cell_bytes _ (BV 64 328) with "C328") as "[C328 %K328]"; [lia|rewrite bv_unsigned_BV; lia|].
  iDestruct (parentHeader_cell_bytes _ (BV 64 336) with "C336") as "[C336 %K336]"; [lia|rewrite bv_unsigned_BV; lia|].
  iDestruct (parentHeader_cell_bytes _ (BV 64 344) with "C344") as "[C344 %K344]"; [lia|rewrite bv_unsigned_BV; lia|].
  iDestruct (parentHeader_cell_bytes _ (BV 64 352) with "C352") as "[C352 %K352]"; [lia|rewrite bv_unsigned_BV; lia|].
  iDestruct (parentHeader_cell_bytes _ (BV 64 360) with "C360") as "[C360 %K360]"; [lia|rewrite bv_unsigned_BV; lia|].
  iDestruct (parentHeader_cell_bytes _ (BV 64 368) with "C368") as "[C368 %K368]"; [lia|rewrite bv_unsigned_BV; lia|].
  iDestruct (parentHeader_cell_bytes _ (BV 64 376) with "C376") as "[C376 %K376]"; [lia|rewrite bv_unsigned_BV; lia|].
  iDestruct (parentHeader_cell_bytes _ (BV 64 384) with "C384") as "[C384 %K384]"; [lia|rewrite bv_unsigned_BV; lia|].
  iDestruct (parentHeader_cell_bytes _ (BV 64 392) with "C392") as "[C392 %K392]"; [lia|rewrite bv_unsigned_BV; lia|].
  parentHeader_join "R F8" 8 40. iDestruct "R" as "[R %J1]".
  parentHeader_join "R F48" 48 272. iDestruct "R" as "[R %J2]".
  parentHeader_join "R C320" 320 8. iDestruct "R" as "[R %J3]".
  parentHeader_join "R C328" 328 8. iDestruct "R" as "[R %J4]".
  parentHeader_join "R C336" 336 8. iDestruct "R" as "[R %J5]".
  parentHeader_join "R C344" 344 8. iDestruct "R" as "[R %J6]".
  parentHeader_join "R C352" 352 8. iDestruct "R" as "[R %J7]".
  parentHeader_join "R C360" 360 8. iDestruct "R" as "[R %J8]".
  parentHeader_join "R C368" 368 8. iDestruct "R" as "[R %J9]".
  parentHeader_join "R C376" 376 8. iDestruct "R" as "[R %J10]".
  parentHeader_join "R C384" 384 8. iDestruct "R" as "[R %J11]".
  parentHeader_join "R C392" 392 8. iDestruct "R" as "[R %J12]".
  lazymatch type of J12 with Z.of_nat (length ?frame) = _ =>
    iExists {| headerExitPath := ParentHeaderMemcpyTail;
               headerResultBytes := parentHeaderMemcpySourceBefore args;
               headerAfterFrame := frame |} end.
  iSplit.
  { iPureIntro. split; [exact Hret|]. split; [exact (Hmeaning args returnAddress after Hret Hwf Hhist)|].
    cbn. split; [lia|reflexivity]. }
  rewrite /parentHeaderExitResources /=.
  assert (Hx2 : bv_add (bv_add (parentHeaderStackPointer args) (BV 64 18446744073709551216)) (BV 64 400) =
                parentHeaderStackPointer args) by bv_solve.
  iEval (rewrite Hx2) in "H2".
  iExists x1, x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  iFrame.
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
  iPoseProof (parentHeader_nextUint64_boxed Hnext with "Hnu") as "#Hnu2".
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
