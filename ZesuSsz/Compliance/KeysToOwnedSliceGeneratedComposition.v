(* keysToOwnedSlice compliance from its block obligations.
   The composition runs over the generated block table
   (KeysToOwnedSliceBlockObligations.v, from tools/block/render_open_blocks.py).
   A slot is closed by the block statement tagged with its address and entry
   constant: a compiled caller lemma (KeysToOwnedSliceClosedBlocks) or a field of
   KeysToOwnedSliceOpenBlocks. Exit design A: every entry carries the contract
   continuation as K; the callers of the three return slots take the generated
   return package at returnAddress, and the end bridge of each slot turns the
   package into the contract exit (outcomes and buffers: ToOwnedSliceBridges.v). *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Automation2.BlockTable.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceContract.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Import ZesuSsz.Compliance.ArrayListBridges.
Require Import ZesuSsz.Compliance.ToOwnedSliceBridges.
Require Import ZesuSsz.Compliance.KeysToOwnedSliceCompositionBoundary.
Require Import ZesuSsz.Compliance.KeysToOwnedSliceBlockObligations.
Require ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0000Entries.
Require ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysToOwnedSliceSelectedCode.
(* reg_col stays folded while the resources are framed. *)
#[local] Typeclasses Opaque reg_col.

(* ---- The block arguments of a contract argument. ---- *)

Definition keysBlockArgsOf (args : ToOwnedSliceArgs) : KeysToOwnedSliceBlockArgs :=
  {| keysBase := args |}.

Lemma keysBlock_wellFormed_of_domain (args : ToOwnedSliceArgs) :
  toOwnedSliceDomain keysElementBytes args ->
  keysBlockArgsWellFormed (keysBlockArgsOf args).
Proof.
  intros Hd.
  pose proof (arrayListWellFormed_capacity_bound keysElementBytes _ ltac:(lia) (proj1 Hd)) as Hcap.
  pose proof (toOwnedSliceDomainRanges _ _ Hd) as
    (Hl & Hitems & Hp & _ & Hr1 & Hr2 & Hr3 & Hl1 & Hl2 & Hl3 & Ha1 & Ha2 & Ha3 &
     Hres & Hscr & Hctx & Hsp16 & Hsplo & Hsphi & Hra4).
  change (mapRamBase defaultMap) with 0xa0000000 in *.
  change (machineRamEnd defaultMap) with 0xc0000000 in *.
  change (mapRamSize defaultMap) with 0x20000000 in *.
  destruct (arrayListHeaderBytes_word_values (toOwnedList args)) as (W0 & W8 & W16); [lia|lia|lia|].
  destruct (altFlAllocatorBytes_words _ Hctx) as (A0 & A8).
  destruct altFlVtableBytes_words as (V0 & _ & V16 & V24).
  unfold keysBlockArgsWellFormed, keysBlockList, keysBlockWord, keysBlockArgsOf; cbn [keysBase].
  split_and!;
    first [ assumption | lia | reflexivity
          | apply arrayListHeaderBytes_length
          | apply Z.mod_divide; [lia|assumption] ].
Qed.

(* ---- Infrastructure (no step names a block). ---- *)

Lemma keysToOwnedSlice_body_weaken `{!islaG Sigma} `{!threadG} (a : Z) (P : iProp Sigma) :
  instr_body a (P ∗ True)%I -∗ instr_body a P.
Proof. iIntros "H". iApply (instr_pre_wand with "H"); [done|done|]. iIntros "$". Qed.

(* An exit block takes the return premise of its generated package from the K
   of its entry. *)
Lemma keysToOwnedSlice_exit_slot `{!islaG Sigma} `{!threadG} (a : Z) (F Kc : iProp Sigma) :
  (Kc -∗ instr_body a ((F ∗ emp) ∗ True)%I) -∗ instr_body a (F ∗ Kc)%I.
Proof.
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "H [HF HK]". iApply ("H" with "HK"). by iFrame.
Qed.

(* ---- Start bridge: the contract entry gives the generated entry state. ---- *)

(* The pure side conditions of the frame steps: bounds, the frame constant,
   and the slot addresses. *)
Ltac keys_side :=
  first [ assumption | reflexivity | lia | (rewrite ?bv_unsigned_BV; lia) | (cbn; lia) ].

Lemma keysToOwnedSlice_start_bridge `{!islaG Sigma} `{!threadG}
    (args : ToOwnedSliceArgs) (returnAddress : Z) :
  (⌜bv_unsigned (toOwnedReturnAddress args) = returnAddress⌝ ∗
   toOwnedSliceEntry keysElementBytes keysLog2Alignment args) ⊢
  ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0
    (keysBlockArgsOf args) returnAddress.
Proof.
  rewrite /toOwnedSliceEntry
    /ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0
    /keysBlockArgsOf /keysBlockList. cbn [keysBase].
  iIntros "[%Hreturn (%x5 & %x6 & %x7 & %x13 & %x14 & %x15 & %x16 & %x17 & %x28 & %x29 & %x30 & %x31 & Hsys & H1 & H2 & H5 & H6 & H7 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H28 & H29 & H30 & H31 & Hsaved & Hheader & Hbuffer & Hresult & Hscratch & Hobject & Hvtable & Hheap & Hframe & %Hd & _)]".
  pose proof (keysBlock_wellFormed_of_domain args Hd) as Hwf.
  pose proof (toOwnedSliceDomainRanges _ _ Hd) as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsplo & Hsphi & Hra4).
  change (mapRamBase defaultMap) with 0xa0000000 in Hsplo.
  set (sp := toOwnedStackPointer args) in *.
  rewrite arrayListSavedRegisters_unfold arrayListBuffer_unfold
    altFlAllocatorObject_unfold altFlVtable_unfold.
  iDestruct "Hsaved" as "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27)".
  iDestruct "Hbuffer" as "(Hitems & Htail & Hblock)".
  (* The 112 bytes: 16 for the allocator callee, 16 scratch, ten saved words. *)
  iDestruct (arrayList_uninit_split _ 16 with "Hframe") as "[Hcallee Hframe]"; [lia|].
  iDestruct (arrayList_uninit_split _ 16 with "Hframe") as "[Hscratch16 Hcells]"; [lia|].
  iDestruct (toOwned_uninit_at _ (bv_unsigned sp - 96 - 16) with "Hcallee") as "Hcallee"; [lia|].
  iDestruct (toOwned_uninit_at _ (bv_unsigned sp - 96) with "Hscratch16") as "Hscratch16"; [lia|].
  iDestruct (toOwned_frame_cell sp (BV 64 18446744073709551520) (BV 64 16) 96 with "Hcells")
    as "[[%w80 Hc16] Hcells]"; [keys_side..|].
  iDestruct (toOwned_frame_cell sp (BV 64 18446744073709551520) (BV 64 24) 96 with "Hcells")
    as "[[%w72 Hc24] Hcells]"; [keys_side..|].
  iDestruct (toOwned_frame_cell sp (BV 64 18446744073709551520) (BV 64 32) 96 with "Hcells")
    as "[[%w64 Hc32] Hcells]"; [keys_side..|].
  iDestruct (toOwned_frame_cell sp (BV 64 18446744073709551520) (BV 64 40) 96 with "Hcells")
    as "[[%w56 Hc40] Hcells]"; [keys_side..|].
  iDestruct (toOwned_frame_cell sp (BV 64 18446744073709551520) (BV 64 48) 96 with "Hcells")
    as "[[%w48 Hc48] Hcells]"; [keys_side..|].
  iDestruct (toOwned_frame_cell sp (BV 64 18446744073709551520) (BV 64 56) 96 with "Hcells")
    as "[[%w40 Hc56] Hcells]"; [keys_side..|].
  iDestruct (toOwned_frame_cell sp (BV 64 18446744073709551520) (BV 64 64) 96 with "Hcells")
    as "[[%w32 Hc64] Hcells]"; [keys_side..|].
  iDestruct (toOwned_frame_cell sp (BV 64 18446744073709551520) (BV 64 72) 96 with "Hcells")
    as "[[%w24 Hc72] Hcells]"; [keys_side..|].
  iDestruct (toOwned_frame_cell sp (BV 64 18446744073709551520) (BV 64 80) 96 with "Hcells")
    as "[[%w16 Hc80] Hcells]"; [keys_side..|].
  iDestruct (toOwned_frame_cell sp (BV 64 18446744073709551520) (BV 64 88) 96 with "Hcells")
    as "[[%w8 Hc88] _]"; [keys_side..|].
  iExists x5, x6, x7, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  iExists w80, w72, w64, w56, w48, w40, w32, w24, w16, w8.
  iFrame. iPureIntro. split_and!.
  - split; [exact Hreturn|exact Hwf].
  - apply Z.mod_divide; [lia|exact Hra4].
  - apply zesu_hist_intro. exists (BV 64 0). split; vm_compute; reflexivity.
Qed.

(* ---- End bridges: each return package gives the contract exit. ---- *)

Lemma keys_Z_to_bv_small (z : Z) : 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma keys_shiftl5 (len : Z) :
  0 <= len <= 2 ^ 24 -> bv_unsigned (bv_shiftl (Z_to_bv 64 len) (BV 64 5)) = len * 32.
Proof.
  intros Hl. rewrite bv_shiftl_unsigned keys_Z_to_bv_small; [|lia].
  change (bv_unsigned (BV 64 5)) with 5. rewrite Z.shiftl_mul_pow2; [|lia].
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma keys_stack_restore (sp : bv 64) :
  bv_add (bv_add sp (BV 64 18446744073709551520)) (BV 64 96) = sp.
Proof. bv_solve. Qed.

(* The frame of every return package as the contract's 112 bytes. *)
Lemma keys_frame_close `{!islaG Sigma} `{!threadG}
    (sp w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : bv 64) :
  112 <= bv_unsigned sp ->
  (bv_unsigned sp - 96) ↦ₘ? 16 -∗
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551520)) (BV 64 16)) ↦ₘ w16 -∗
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551520)) (BV 64 24)) ↦ₘ w24 -∗
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551520)) (BV 64 32)) ↦ₘ w32 -∗
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551520)) (BV 64 40)) ↦ₘ w40 -∗
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551520)) (BV 64 48)) ↦ₘ w48 -∗
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551520)) (BV 64 56)) ↦ₘ w56 -∗
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551520)) (BV 64 64)) ↦ₘ w64 -∗
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551520)) (BV 64 72)) ↦ₘ w72 -∗
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551520)) (BV 64 80)) ↦ₘ w80 -∗
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551520)) (BV 64 88)) ↦ₘ w88 -∗
  (bv_unsigned sp - 96 - 16) ↦ₘ? 16 -∗
  (bv_unsigned sp - 112) ↦ₘ? 112.
Proof.
  iIntros (Hsp) "Hs H16 H24 H32 H40 H48 H56 H64 H72 H80 H88 Hcallee".
  assert (Hc : bv_unsigned (BV 64 18446744073709551520) = 2 ^ 64 - 96) by reflexivity.
  iDestruct (toOwned_cell_uninit sp _ _ 96 with "H16") as "H16"; [keys_side..|].
  iDestruct (toOwned_cell_uninit sp _ _ 96 with "H24") as "H24"; [keys_side..|].
  iDestruct (toOwned_cell_uninit sp _ _ 96 with "H32") as "H32"; [keys_side..|].
  iDestruct (toOwned_cell_uninit sp _ _ 96 with "H40") as "H40"; [keys_side..|].
  iDestruct (toOwned_cell_uninit sp _ _ 96 with "H48") as "H48"; [keys_side..|].
  iDestruct (toOwned_cell_uninit sp _ _ 96 with "H56") as "H56"; [keys_side..|].
  iDestruct (toOwned_cell_uninit sp _ _ 96 with "H64") as "H64"; [keys_side..|].
  iDestruct (toOwned_cell_uninit sp _ _ 96 with "H72") as "H72"; [keys_side..|].
  iDestruct (toOwned_cell_uninit sp _ _ 96 with "H80") as "H80"; [keys_side..|].
  iDestruct (toOwned_cell_uninit sp _ _ 96 with "H88") as "H88"; [keys_side..|].
  iDestruct (toOwned_uninit_join_at _ _ 8 8 16 with "H80 H88") as "H"; [keys_side..|].
  iDestruct (toOwned_uninit_join_at _ _ 8 16 24 with "H72 H") as "H"; [keys_side..|].
  iDestruct (toOwned_uninit_join_at _ _ 8 24 32 with "H64 H") as "H"; [keys_side..|].
  iDestruct (toOwned_uninit_join_at _ _ 8 32 40 with "H56 H") as "H"; [keys_side..|].
  iDestruct (toOwned_uninit_join_at _ _ 8 40 48 with "H48 H") as "H"; [keys_side..|].
  iDestruct (toOwned_uninit_join_at _ _ 8 48 56 with "H40 H") as "H"; [keys_side..|].
  iDestruct (toOwned_uninit_join_at _ _ 8 56 64 with "H32 H") as "H"; [keys_side..|].
  iDestruct (toOwned_uninit_join_at _ _ 8 64 72 with "H24 H") as "H"; [keys_side..|].
  iDestruct (toOwned_uninit_join_at _ _ 8 72 80 with "H16 H") as "H"; [keys_side..|].
  iDestruct (toOwned_uninit_join_at _ _ 16 80 96 with "Hs H") as "H"; [keys_side..|].
  iDestruct (toOwned_uninit_join_at _ _ 16 96 112 with "Hcallee H") as "H"; [keys_side..|].
  iApply (toOwned_uninit_at with "H"). lia.
Qed.

(* The scratch bytes of a package that stored the overflow flag byte. *)
Lemma keys_scratch_close `{!islaG Sigma} `{!threadG} (sp : Z) (b : byte) :
  sp ↦ₘ? 8 -∗ (sp + 8) ↦ₘ∗ [b] -∗ (sp + 9) ↦ₘ? 7 -∗ sp ↦ₘ? 16.
Proof.
  iIntros "H0 Hb H9". iDestruct (arrayList_bytes_uninit with "Hb") as "Hb".
  iDestruct (toOwned_uninit_join_at _ _ 8 _ 9 with "H0 Hb") as "H"; [keys_side..|].
  iApply (toOwned_uninit_join_at _ _ 9 7 16 with "H H9"); keys_side.
Qed.

Definition keysExit `{!islaG Sigma} `{!threadG} (args : ToOwnedSliceArgs) (returnAddress : Z) :
    iProp Sigma :=
  (∃ outcome : ToOwnedSliceOutcome,
    ⌜bv_unsigned (toOwnedReturnAddress args) = returnAddress /\
      toOwnedSliceDomain keysElementBytes args /\
      toOwnedSliceAllows keysElementBytes keysEmptyPointer args outcome⌝ ∗
    toOwnedSliceExit keysElementBytes keysLog2Alignment args outcome)%I.

(* Slot 0: allocation failed; the list keeps its buffer, error.OutOfMemory. *)
Lemma keys_end_bridge_slot0 `{!islaG Sigma} `{!threadG} (args : ToOwnedSliceArgs) (returnAddress : Z) :
  ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0
    (keysBlockArgsOf args) returnAddress ⊢ keysExit args returnAddress.
Proof.
  rewrite /ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0
    /keysBlockDomainAt /keysBlockList /keysBlockArgsOf. cbn [keysBase].
  iIntros "(%m5 & %m6 & %m7 & %m11 & %m12 & %m13 & %m14 & %m15 & %m16 & %m17 & %m28 & %m29 & %m30 & %m31 & Hsys & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hheader & Hitems & Htail & Hblock & Hresult & Hobject & Hvtable & Hheap & Hscratch & Hs8 & Hbyte & Hs7 & Hc16 & Hc24 & Hc32 & Hc40 & Hc48 & Hc56 & Hc64 & Hc72 & Hc80 & Hc88 & Hcallee & %Hdom & _ & %Hlen & _)".
  destruct Hdom as [Hret Hwf]. pose proof Hwf as (_ & _ & _ & _ & _ & Hd & _). cbn [keysBase] in Hd.
  pose proof (toOwnedSliceDomainRanges _ _ Hd) as
    (Hl & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsplo & Hsphi & _).
  change (mapRamBase defaultMap) with 0xa0000000 in Hsplo.
  destruct Hlen as [_ Hlen]. rewrite keys_Z_to_bv_small in Hlen; [|pose proof (arrayListWellFormed_capacity_bound keysElementBytes _ ltac:(lia) (proj1 Hd)) as Hcap; change (mapRamSize defaultMap) with 0x20000000 in Hcap; lia].
  iDestruct (keys_scratch_close with "Hs8 Hbyte Hs7") as "Hs".
  iDestruct (keys_frame_close with "Hs Hc16 Hc24 Hc32 Hc40 Hc48 Hc56 Hc64 Hc72 Hc80 Hc88 Hcallee")
    as "Hframe"; [lia|].
  rewrite keys_stack_restore.
  iEval (rewrite toOwned_error_image) in "Hresult".
  iPoseProof (toOwned_empty_buffer keysElementBytes keysLog2Alignment keysEmptyPointer ltac:(lia))
    as "Hslice".
  iExists (toOwnedOutOfMemoryOutcome keysEmptyPointer args). iSplit.
  { iPureIntro. split_and!; [exact Hret|exact Hd|].
    apply toOwnedOutOfMemory_allows; [lia|exact Hd|exact Hlen]. }
  rewrite /toOwnedSliceExit toOwnedOutOfMemory_scratch.
  iExists m5, m6, m7, (BV 64 2), m11, m12, m13, m14, m15, m16, m17, m28, m29, m30, m31.
  rewrite /toOwnedOutOfMemoryOutcome. cbn [toOwnedListAfter toOwnedSlice toOwnedResultAfter].
  rewrite arrayListSavedRegisters_unfold /altFlAllocatorObject /altFlVtable
    (arrayListBuffer_unfold _ _ (toOwnedList args)).
  change (96 + 16) with 112.
  iFrame. iExact "Hslice".
Qed.

(* Slot 1: length 0; the list is reset to the empty list, the old pointer is returned. *)
Lemma keys_end_bridge_slot1 `{!islaG Sigma} `{!threadG} (args : ToOwnedSliceArgs) (returnAddress : Z) :
  ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0
    (keysBlockArgsOf args) returnAddress ⊢ keysExit args returnAddress.
Proof.
  rewrite /ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0
    /keysBlockDomainAt /keysBlockList /keysBlockArgsOf. cbn [keysBase].
  iIntros "(%m5 & %m6 & %m7 & %m12 & %m13 & %m14 & %m15 & %m16 & %m17 & %m28 & %m29 & %m30 & %m31 & Hsys & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hheader & Hresult & Hobject & Hvtable & Hheap & Hscratch & Hs & Hc16 & Hc24 & Hc32 & Hc40 & Hc48 & Hc56 & Hc64 & Hc72 & Hc80 & Hc88 & Hcallee & %Hdom & _ & %Hlen & _)".
  destruct Hdom as [Hret Hwf]. pose proof Hwf as (_ & _ & _ & _ & _ & Hd & _). cbn [keysBase] in Hd.
  pose proof (toOwnedSliceDomainRanges _ _ Hd) as
    (Hl & _ & Hp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsplo & Hsphi & _).
  change (mapRamBase defaultMap) with 0xa0000000 in Hsplo.
  pose proof (arrayListWellFormed_capacity_bound keysElementBytes _ ltac:(lia) (proj1 Hd)) as Hcap.
  change (mapRamSize defaultMap) with 0x20000000 in Hcap.
  destruct Hlen as [_ Hlen]. rewrite keys_Z_to_bv_small in Hlen; [|lia].
  iDestruct (keys_frame_close with "Hs Hc16 Hc24 Hc32 Hc40 Hc48 Hc56 Hc64 Hc72 Hc80 Hc88 Hcallee")
    as "Hframe"; [lia|].
  rewrite keys_stack_restore.
  iEval (rewrite toOwned_header_reset) in "Hheader".
  iEval (rewrite toOwned_result_image keys_Z_to_bv_small; [|lia]) in "Hresult".
  iPoseProof (toOwned_empty_buffer keysElementBytes keysLog2Alignment keysEmptyPointer ltac:(lia))
    as "Hlist".
  iPoseProof (toOwned_empty_buffer keysElementBytes keysLog2Alignment
    (arrayListPointer (toOwnedList args)) ltac:(lia)) as "Hslice".
  iExists (toOwnedEmptyOutcome keysEmptyPointer args). iSplit.
  { iPureIntro. split_and!; [exact Hret|exact Hd|].
    apply toOwnedEmpty_allows; [lia|exact Hd|exact Hlen]. }
  rewrite /toOwnedSliceExit toOwnedEmpty_scratch; [|exact Hlen].
  iExists m5, m6, m7, (BV 64 0), (BV 64 1), m12, m13, m14, m15, m16, m17, m28, m29, m30, m31.
  rewrite /toOwnedEmptyOutcome. cbn [toOwnedListAfter toOwnedSlice toOwnedResultAfter].
  rewrite arrayListSavedRegisters_unfold /altFlAllocatorObject /altFlVtable.
  change (96 + 16) with 112.
  iFrame. iSplitL; [iExact "Hlist"|iExact "Hslice"].
Qed.

(* Slot 2: the items are copied to a new block; the list keeps its pointer
   with length and capacity 0. *)
Lemma keys_end_bridge_slot2 `{!islaG Sigma} `{!threadG} (args : ToOwnedSliceArgs) (returnAddress : Z) :
  ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0
    (keysBlockArgsOf args) returnAddress ⊢ keysExit args returnAddress.
Proof.
  rewrite /ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0
    /keysBlockDomainAt /keysBlockList /keysBlockArgsOf. cbn [keysBase].
  iIntros "(%c5 & %c6 & %c7 & %c10 & %c11 & %c12 & %c13 & %c14 & %c15 & %c16 & %c17 & %c28 & %c29 & %c30 & %c31 & %p & Hsys & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hheader & Hresult & Hobject & Hvtable & Hheap & Hscratch & Hs8 & Hbyte & Hs7 & Hc16 & Hc24 & Hc32 & Hc40 & Hc48 & Hc56 & Hc64 & Hc72 & Hc80 & Hc88 & Hcallee & Hcopy & Hblock & %Hdom & _ & _ & _ & _ & %Hlen & _ & _ & %Hp & _ & _ & _ & %Hhist)".
  destruct Hdom as [Hret Hwf]. pose proof Hwf as (_ & _ & _ & _ & _ & Hd & _). cbn [keysBase] in Hd.
  pose proof (toOwnedSliceDomainRanges _ _ Hd) as
    (Hl & Hitems & Hold & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsplo & Hsphi & _).
  change (mapRamBase defaultMap) with 0xa0000000 in Hsplo.
  pose proof (arrayListWellFormed_capacity_bound keysElementBytes _ ltac:(lia) (proj1 Hd)) as Hcap.
  change (mapRamSize defaultMap) with 0x20000000 in Hcap.
  destruct Hlen as [_ Hlen]. rewrite keys_Z_to_bv_small in Hlen; [|lia].
  destruct Hp as [_ Hp].
  apply zesu_hist_elim in Hhist.
  unfold ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0_Hist in Hhist.
  unfold keysBlockList, keysBlockArgsOf in Hhist. cbn [keysBase] in Hhist.
  destruct Hhist as (? & ? & ? & ? & ? & ? & ? & ? & Halloc & _).
  rewrite keys_shiftl5 in Halloc; [|lia].
  rewrite keys_shiftl5; [|lia].
  rewrite -Halloc Hitems.
  iEval (rewrite altFlBlock_unfold) in "Hblock". iDestruct "Hblock" as "[Hslack %Hfacts]".
  destruct (Hfacts ltac:(lia)) as (Hlo & Hhi & _).
  pose proof (altFlBlockSlack_nonneg (arrayListLength (toOwnedList args) * keysElementBytes)
    (bv_unsigned (BV 64 0))) as Hslack.
  change (mapRamBase defaultMap) with 0xa0000000 in Hlo.
  change (machineRamEnd defaultMap) with 0xc0000000 in Hhi.
  iAssert (altFlBlock (bv_unsigned p) (arrayListLength (toOwnedList args) * keysElementBytes)
    keysLog2Alignment) with "[Hslack]" as "Hblock".
  { rewrite altFlBlock_unfold. iFrame. iPureIntro. exact Hfacts. }
  iPoseProof (toOwned_copied_buffer keysElementBytes keysLog2Alignment args (bv_unsigned p) Hitems
    with "Hcopy Hblock") as "Hslice".
  iDestruct (keys_scratch_close with "Hs8 Hbyte Hs7") as "Hs".
  iDestruct (keys_frame_close with "Hs Hc16 Hc24 Hc32 Hc40 Hc48 Hc56 Hc64 Hc72 Hc80 Hc88 Hcallee")
    as "Hframe"; [lia|].
  rewrite keys_stack_restore.
  iEval (rewrite toOwned_header_clear) in "Hheader".
  iEval (rewrite keys_Z_to_bv_small; [|lia]) in "Hresult".
  iEval (rewrite toOwned_result_image) in "Hresult".
  iPoseProof (toOwned_empty_buffer keysElementBytes keysLog2Alignment
    (arrayListPointer (toOwnedList args)) ltac:(lia)) as "Hlist".
  iExists (toOwnedSuccessOutcome args (bv_unsigned p)). iSplit.
  { iPureIntro. split_and!; [exact Hret|exact Hd|].
    apply toOwnedSuccess_allows; [exact Hd|exact Hlen| |].
    - pose proof (bv_unsigned_in_range _ p) as Hpr. unfold bv_modulus in Hpr. cbn in Hpr. lia.
    - unfold arrayListRamRange. change (mapRamBase defaultMap) with 0xa0000000.
      change (machineRamEnd defaultMap) with 0xc0000000. lia. }
  rewrite /toOwnedSliceExit toOwnedSuccess_scratch; [|exact Hlen].
  iExists c5, c6, c7, c10, c11, c12, c13, c14, c15, c16, c17, c28, c29, c30, c31.
  rewrite /toOwnedSuccessOutcome. cbn [toOwnedListAfter toOwnedSlice toOwnedResultAfter].
  rewrite arrayListSavedRegisters_unfold /altFlAllocatorObject /altFlVtable.
  change (96 + 16) with 112.
  iFrame. all: first [iExact "Hlist" | iExact "Hslice"].
Qed.

(* ---- Composition over the block table. ---- *)

(* The membership of a slot: address and state both match (the slots of one
   block share its address); the index is found syntactically. *)
Ltac keysToOwnedSlice_index entry entries :=
  lazymatch entries with
  | entry :: _ => constr:(0%nat)
  | _ :: ?rest => let n := keysToOwnedSlice_index entry rest in constr:(S n)
  end.
Ltac keysToOwnedSlice_member :=
  lazymatch goal with
  | |- ?entry ∈ ?entries =>
      let n := keysToOwnedSlice_index entry entries in
      exact (elem_of_list_lookup_2 entries n entry eq_refl)
  end.

(* A premise is chosen by its address: the callee specs by their symbols, a
   successor by table lookup. A return premise (address returnAddress, a
   variable) is no table slot and fails at once. *)
Ltac keysToOwnedSlice_premise :=
  lazymatch goal with
  | |- environments.envs_entails _ (instr_pre ?a _) =>
      tryif is_var a then fail else
      tryif (let s := constr:(sym_alt_fl_alloc_alloc) in constr_eq a s) then iExact "Halloc" else
      tryif (let s := constr:(sym_alt_fl_alloc_remap) in constr_eq a s) then iExact "Hremap" else
      tryif (let s := constr:(sym_alt_fl_alloc_free) in constr_eq a s) then iExact "Hfree" else
      tryif (let s := constr:(sym_memcpy) in constr_eq a s) then iExact "Hmemcpy" else
      solve [ iApply (block_table_pre_lookup with "Htab");
              unfold keysToOwnedSliceBlockTable; cbn [block_table_entries];
              keysToOwnedSlice_member ]
  | |- _ => iExact "Hsel"
  end.

(* The return premise of a return package from the contract continuation:
   the package's end bridge gives the contract exit. The bridge is chosen by
   the package's name. *)
Ltac keysToOwnedSlice_exit_premise H :=
  iEval (rewrite /keysToOwnedSliceContinuation) in H;
  iApply (instr_pre_wand with H); [done|done|];
  unfold ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot0,
    ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot1,
    ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot2;
  iIntros "[Hexit _]";
  lazymatch iTypeOf (INamed "Hexit") with
  | Some (_, @ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 _ _ _ _ _) =>
      iApply (keys_end_bridge_slot0 with "Hexit")
  | Some (_, @ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 _ _ _ _ _) =>
      iApply (keys_end_bridge_slot1 with "Hexit")
  | Some (_, @ZesuSsz.Generated.KeysToOwnedSlice.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 _ _ _ _ _) =>
      iApply (keys_end_bridge_slot2 with "Hexit")
  end.

(* The generic slot step: the block statement tagged with the slot's address
   and entry constant. Its successor premises come from the table, its callee
   and code premises from the table code; an exit block's return premise
   comes from K through the package's end bridge. *)
Ltac keysToOwnedSlice_slot :=
  iIntros "#Htab";
  iPoseProof (block_table_pre_code with "Htab") as "#Hcode";
  iEval (unfold keysToOwnedSliceBlockTable; cbn [block_table_code];
         unfold keysToOwnedSliceTableCode) in "Hcode";
  iDestruct "Hcode" as "(Hsel & Halloc & Hremap & Hfree & Hmemcpy)";
  lazymatch goal with
  | |- environments.envs_entails _ (instr_body ?address (?entry _ _ _)) =>
      lazymatch goal with
      | H : keysToOwnedSliceBlockAt address entry _ |- _ =>
          let statement := fresh "Hstatement" in
          pose proof H as statement; unfold keysToOwnedSliceBlockAt in statement;
          first
          [ iApply keysToOwnedSlice_body_weaken; iApply statement; keysToOwnedSlice_premise
          | iApply keysToOwnedSlice_exit_slot; iIntros "Hret";
            iApply (statement with "[Hret]");
            [ keysToOwnedSlice_exit_premise "Hret" | keysToOwnedSlice_premise .. ] ]
      end
  end.

Ltac keysToOwnedSlice_block_statements Sigma Hopen :=
  pose proof keysToOwnedSliceClosedBlocks as Hclosed;
  destruct Hclosed; destruct Hopen;
  repeat match goal with
  | H : forall _ : gFunctors, _ |- _ => specialize (H Sigma _ _)
  end.

Lemma keysToOwnedSlice_entry_body `{!islaG Sigma} `{!threadG} :
  KeysToOwnedSliceOpenBlocks ->
  forall (args : ToOwnedSliceArgs) (returnAddress : Z),
  ⊢ □ keysToOwnedSliceTableCode -∗
    instr_body sym_array_list_Aligned_32_u8_null_toOwnedSlice
      (ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0000Entries.fp_machineAt0000
        (keysBlockArgsOf args) returnAddress
        (keysToOwnedSliceContinuation (keysBlockArgsOf args) returnAddress)).
Proof.
  intros Hopen args returnAddress.
  keysToOwnedSlice_block_statements Sigma Hopen.
  iIntros "#Htop".
  iApply (block_table_body (keysToOwnedSliceBlockTable (keysBlockArgsOf args) returnAddress)).
  { unfold keysToOwnedSliceBlockTable; cbn [block_table_entries]. keysToOwnedSlice_member. }
  { iModIntro. iExact "Htop". }
  iModIntro. iIntros (address state Hin).
  unfold keysToOwnedSliceBlockTable in Hin; cbn [block_table_entries] in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]).
  all: try (apply elem_of_nil in Hin as []).
  all: injection Hin as Haddress Hstate; subst address state.
  all: keysToOwnedSlice_slot.
Qed.

(* ---- The theorem, given the open blocks. ---- *)
Theorem keysToOwnedSliceGeneratedCompliance :
  KeysToOwnedSliceOpenBlocks ->
  KeysToOwnedSliceContractCorrect.
Proof.
  intros Hopen returnAddress Sigma HG HT.
  change (⊢ keysToOwnedSliceContractCode -∗ ∀ args : ToOwnedSliceArgs,
    instr_body sym_array_list_Aligned_32_u8_null_toOwnedSlice
      ((⌜bv_unsigned (toOwnedReturnAddress args) = returnAddress⌝ ∗
        toOwnedSliceEntry keysElementBytes keysLog2Alignment args) ∗
       keysToOwnedSliceContinuation (keysBlockArgsOf args) returnAddress))%I.
  rewrite /keysToOwnedSliceContractCode /altFlAllocatorPremises /altFlAllocCallPremise
    /altFlRemapCallPremise /altFlFreeCallPremise /ziskMemcpyCallPremise.
  iIntros "(#Hsel & (#Halloc & #Hremap & #Hfree) & #Hmemcpy)" (args).
  iPoseProof (keysToOwnedSlice_entry_body Hopen args returnAddress with "[]") as "Hbody".
  { iModIntro. unfold keysToOwnedSliceTableCode. iFrame "#". }
  iApply (instr_pre_wand with "Hbody"); [done|done|].
  iIntros "[Hentry Hcontinuation]".
  rewrite /ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0000Entries.fp_machineAt0000.
  iFrame "Hcontinuation".
  by iApply (keysToOwnedSlice_start_bridge with "Hentry").
Qed.
