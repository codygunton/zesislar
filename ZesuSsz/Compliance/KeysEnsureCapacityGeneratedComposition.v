(* keysEnsureCapacity compliance from its block obligations.
   The composition runs over the generated block table
   (KeysEnsureCapacityBlockObligations.v, from tools/block/render_open_blocks.py).
   A slot is closed by the block statement tagged with its address and entry
   constant: a compiled caller lemma (KeysEnsureCapacityClosedBlocks) or a field
   of KeysEnsureCapacityOpenBlocks. Every entry carries the contract
   postcondition as K (keysEnsureCapacityContinuation); the three return slots
   of the duplicated join 0x008c take their return packages as premises, which
   the end bridges below derive from K. The start bridge turns the contract
   entry into block 0x0000's entry. Hand-written by the region owner; the
   array-list facts it uses are in ArrayListBridges.v. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Automation2.BlockTable.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityContract.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityBlockEntries.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Compliance.ArrayListBridges.
Require Import ZesuSsz.Compliance.KeysEnsureCapacityCompositionBoundary.
Require Import ZesuSsz.Compliance.KeysEnsureCapacityBlockObligations.
Require ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0000Entries.
Require ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent keysEnsureCapacitySelectedCode.

(* ---- Ranges of the block arguments. ---- *)

Lemma keysEnsureCapacity_block_wellformed (base : EnsureCapacityArgs) :
  keysEnsureCapacityDomain base ->
  ensureBlockArgsWellFormed {| ensureBase := base |}.
Proof.
  intros Hd. pose proof Hd as Hd'.
  destruct Hd' as (Hwf & Hlist & Hla & Halloc & Haa & Hctx & Hreq & Hscr & Hstack & Hret).
  pose proof (arrayListWellFormed_capacity_bound 32 (ensureList base) ltac:(lia) Hwf) as Hcap.
  destruct Hwf as (Hlen & Hitems & Hptr & _).
  unfold arrayListRamRange, arrayListStackLayout, machineRamEnd in *.
  destruct Hstack as (Hsp16 & Hsplo & Hsphi).
  pose proof (bv_unsigned_in_range _ (ensureListPointer base)).
  pose proof (bv_unsigned_in_range _ (ensureAllocatorPointer base)).
  pose proof (bv_unsigned_in_range _ (ensureStackPointer base)).
  pose proof (bv_unsigned_in_range _ (ensureRequested base)).
  unfold bv_modulus in *.
  cbn [mapRamBase mapRamSize defaultMap] in *.
  unfold ensureBlockArgsWellFormed, ensureBlockList, ensureBlockWord; cbn [ensureBase].
  destruct (arrayListHeaderBytes_word_values (ensureList base)) as (Hw0 & Hw8 & Hw16); [lia|lia|lia|].
  destruct (altFlAllocatorBytes_words (ensureAllocatorContext base)) as (Ha0 & Ha8); [lia|].
  destruct altFlVtableBytes_words as (Hv0 & _ & Hv16 & Hv24).
  rewrite drop_0 in Hw0 Ha0 Hv0.
  split_and!; try assumption; try lia;
    try (apply Z.mod_divide; [lia|]; assumption);
    try (rewrite Z.mod_divide; [assumption|lia]).
  all: try (cbn [Z.to_nat Pos.to_nat]; first [exact Hw0|exact Hw8|exact Hw16|exact Ha0|exact Ha8|exact Hv0|exact Hv16|exact Hv24]).
  all: first [apply arrayListHeaderBytes_length|apply altFlAllocatorBytes_length].
Qed.

Lemma ensure_frame_address (sp c d : bv 64) :
  128 <= bv_unsigned sp -> bv_unsigned c = 18446744073709551504 -> bv_unsigned d < 112 ->
  bv_unsigned (bv_add (bv_add sp c) d) = bv_unsigned sp - 112 + bv_unsigned d.
Proof.
  intros Hsp Hc Hd. pose proof (bv_unsigned_in_range _ sp) as Hr.
  pose proof (bv_unsigned_in_range _ d) as Hdr. unfold bv_modulus in *.
  rewrite !bv_add_unsigned Hc. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in *.
  replace (bv_unsigned sp + 18446744073709551504) with
    ((bv_unsigned sp - 112) + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. rewrite (Z.mod_small (bv_unsigned sp - 112)); [|lia].
  apply Z.mod_small. lia.
Qed.

Lemma ensure_frame_open `{!islaG Sigma} `{!threadG} (sp : Z) :
  (sp - (112 + 16)) ↦ₘ? (112 + 16) -∗
  (sp - 112 - 16) ↦ₘ? 16 ∗ (sp - 112) ↦ₘ? 24 ∗
  ∃ w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 : bv 64,
   (sp - 112 + 24) ↦ₘ w88 ∗
   (sp - 112 + 32) ↦ₘ w80 ∗
   (sp - 112 + 40) ↦ₘ w72 ∗
   (sp - 112 + 48) ↦ₘ w64 ∗
   (sp - 112 + 56) ↦ₘ w56 ∗
   (sp - 112 + 64) ↦ₘ w48 ∗
   (sp - 112 + 72) ↦ₘ w40 ∗
   (sp - 112 + 80) ↦ₘ w32 ∗
   (sp - 112 + 88) ↦ₘ w24 ∗
   (sp - 112 + 96) ↦ₘ w16 ∗
   (sp - 112 + 104) ↦ₘ w8.
Proof.
  iIntros "H".
  iDestruct (arrayList_uninit_split _ 16 with "H") as "[H0 H]"; [lia|].
  replace (sp - (112 + 16) + 16) with (sp - 112) by lia.
  replace (112 + 16 - 16) with 112 by lia.
  replace (sp - (112 + 16)) with (sp - 112 - 16) by lia. iFrame "H0".
  iDestruct (arrayList_uninit_split _ 24 with "H") as "[$ H]"; [lia|].
  replace (112 - 24) with 88 by lia.
  iDestruct (arrayList_uninit_split _ 8 with "H") as "[W24 H]"; [lia|].
  replace (sp - 112 + 24 + 8) with (sp - 112 + 32) by lia. replace (88 - 8) with 80 by lia.
  iDestruct (arrayList_uninit_word with "W24") as (w88) "W24".
  iDestruct (arrayList_uninit_split _ 8 with "H") as "[W32 H]"; [lia|].
  replace (sp - 112 + 32 + 8) with (sp - 112 + 40) by lia. replace (80 - 8) with 72 by lia.
  iDestruct (arrayList_uninit_word with "W32") as (w80) "W32".
  iDestruct (arrayList_uninit_split _ 8 with "H") as "[W40 H]"; [lia|].
  replace (sp - 112 + 40 + 8) with (sp - 112 + 48) by lia. replace (72 - 8) with 64 by lia.
  iDestruct (arrayList_uninit_word with "W40") as (w72) "W40".
  iDestruct (arrayList_uninit_split _ 8 with "H") as "[W48 H]"; [lia|].
  replace (sp - 112 + 48 + 8) with (sp - 112 + 56) by lia. replace (64 - 8) with 56 by lia.
  iDestruct (arrayList_uninit_word with "W48") as (w64) "W48".
  iDestruct (arrayList_uninit_split _ 8 with "H") as "[W56 H]"; [lia|].
  replace (sp - 112 + 56 + 8) with (sp - 112 + 64) by lia. replace (56 - 8) with 48 by lia.
  iDestruct (arrayList_uninit_word with "W56") as (w56) "W56".
  iDestruct (arrayList_uninit_split _ 8 with "H") as "[W64 H]"; [lia|].
  replace (sp - 112 + 64 + 8) with (sp - 112 + 72) by lia. replace (48 - 8) with 40 by lia.
  iDestruct (arrayList_uninit_word with "W64") as (w48) "W64".
  iDestruct (arrayList_uninit_split _ 8 with "H") as "[W72 H]"; [lia|].
  replace (sp - 112 + 72 + 8) with (sp - 112 + 80) by lia. replace (40 - 8) with 32 by lia.
  iDestruct (arrayList_uninit_word with "W72") as (w40) "W72".
  iDestruct (arrayList_uninit_split _ 8 with "H") as "[W80 H]"; [lia|].
  replace (sp - 112 + 80 + 8) with (sp - 112 + 88) by lia. replace (32 - 8) with 24 by lia.
  iDestruct (arrayList_uninit_word with "W80") as (w32) "W80".
  iDestruct (arrayList_uninit_split _ 8 with "H") as "[W88 H]"; [lia|].
  replace (sp - 112 + 88 + 8) with (sp - 112 + 96) by lia. replace (24 - 8) with 16 by lia.
  iDestruct (arrayList_uninit_word with "W88") as (w24) "W88".
  iDestruct (arrayList_uninit_split _ 8 with "H") as "[W96 H]"; [lia|].
  replace (sp - 112 + 96 + 8) with (sp - 112 + 104) by lia. replace (16 - 8) with 8 by lia.
  iDestruct (arrayList_uninit_word with "W96") as (w16) "W96".
  iDestruct (arrayList_uninit_word with "H") as (w8) "W104".
  iExists w88, w80, w72, w64, w56, w48, w40, w32, w24, w16, w8. iFrame.
Qed.

Ltac ensure_frame_addresses Hsp :=
  repeat match goal with
  | |- context [bv_unsigned (bv_add (bv_add ?sp ?c) ?d)] =>
      rewrite (ensure_frame_address sp c d Hsp); [|reflexivity|cbn; lia]
  end;
  cbn [bv_unsigned].

Lemma keysEnsureCapacity_stack_bound (base : EnsureCapacityArgs) :
  keysEnsureCapacityDomain base -> 128 <= bv_unsigned (ensureStackPointer base).
Proof.
  intros Hd. destruct Hd as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & Hlo & _) & _).
  cbn in Hlo. lia.
Qed.

Lemma keysEnsureCapacity_start_bridge `{!islaG Sigma} `{!threadG}
    (base : EnsureCapacityArgs) (returnAddress : Z) :
  (⌜bv_unsigned (ensureReturnAddress base) = returnAddress⌝ ∗ keysEnsureCapacityEntry base) ⊢
  ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0 {| ensureBase := base |} returnAddress.
Proof.
  rewrite /keysEnsureCapacityEntry /ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0.
  iIntros "[%Hret (%x5 & %x6 & %x7 & %x13 & %x14 & %x15 & %x16 & %x17 & %x28 & %x29 & %x30 & %x31 & Hsys & H1 & H2 & H5 & H6 & H7 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H28 & H29 & H30 & H31 & Hsaved & Hhdr & Hbuf & Hscr & Halloc & Hvt & Hheap & Hframe & %Hd & _)]".
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
  - apply zesu_hist_intro. unfold ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0_Hist.
    exists (BV 64 0). split; vm_compute; reflexivity.
Qed.

Lemma ensure_frame_close `{!islaG Sigma} `{!threadG} (sp : Z) (w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 : bv 64) :
  (sp - 112 - 16) ↦ₘ? 16 -∗ (sp - 112) ↦ₘ? 24 -∗
  (sp - 112 + 24) ↦ₘ w88 -∗
  (sp - 112 + 32) ↦ₘ w80 -∗
  (sp - 112 + 40) ↦ₘ w72 -∗
  (sp - 112 + 48) ↦ₘ w64 -∗
  (sp - 112 + 56) ↦ₘ w56 -∗
  (sp - 112 + 64) ↦ₘ w48 -∗
  (sp - 112 + 72) ↦ₘ w40 -∗
  (sp - 112 + 80) ↦ₘ w32 -∗
  (sp - 112 + 88) ↦ₘ w24 -∗
  (sp - 112 + 96) ↦ₘ w16 -∗
  (sp - 112 + 104) ↦ₘ w8 -∗
  (sp - (112 + 16)) ↦ₘ? (112 + 16).
Proof.
  iIntros "Hcallee Hscratch W24 W32 W40 W48 W56 W64 W72 W80 W88 W96 W104".
  iDestruct (arrayList_word_uninit with "W24") as "W24".
  iDestruct (arrayList_word_uninit with "W32") as "W32".
  iDestruct (arrayList_word_uninit with "W40") as "W40".
  iDestruct (arrayList_word_uninit with "W48") as "W48".
  iDestruct (arrayList_word_uninit with "W56") as "W56".
  iDestruct (arrayList_word_uninit with "W64") as "W64".
  iDestruct (arrayList_word_uninit with "W72") as "W72".
  iDestruct (arrayList_word_uninit with "W80") as "W80".
  iDestruct (arrayList_word_uninit with "W88") as "W88".
  iDestruct (arrayList_word_uninit with "W96") as "W96".
  iDestruct (arrayList_word_uninit with "W104") as "W104".
  iRename "W104" into "H".
  replace (sp - 112 + 104) with (sp - 112 + 96 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W96 H") as "H"; [lia|lia|].
  replace (8 + 8) with 16 by lia.
  replace (sp - 112 + 96) with (sp - 112 + 88 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W88 H") as "H"; [lia|lia|].
  replace (8 + 16) with 24 by lia.
  replace (sp - 112 + 88) with (sp - 112 + 80 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W80 H") as "H"; [lia|lia|].
  replace (8 + 24) with 32 by lia.
  replace (sp - 112 + 80) with (sp - 112 + 72 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W72 H") as "H"; [lia|lia|].
  replace (8 + 32) with 40 by lia.
  replace (sp - 112 + 72) with (sp - 112 + 64 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W64 H") as "H"; [lia|lia|].
  replace (8 + 40) with 48 by lia.
  replace (sp - 112 + 64) with (sp - 112 + 56 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W56 H") as "H"; [lia|lia|].
  replace (8 + 48) with 56 by lia.
  replace (sp - 112 + 56) with (sp - 112 + 48 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W48 H") as "H"; [lia|lia|].
  replace (8 + 56) with 64 by lia.
  replace (sp - 112 + 48) with (sp - 112 + 40 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W40 H") as "H"; [lia|lia|].
  replace (8 + 64) with 72 by lia.
  replace (sp - 112 + 40) with (sp - 112 + 32 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W32 H") as "H"; [lia|lia|].
  replace (8 + 72) with 80 by lia.
  replace (sp - 112 + 32) with (sp - 112 + 24 + 8) by lia.
  iDestruct (arrayList_uninit_join with "W24 H") as "H"; [lia|lia|].
  replace (8 + 80) with 88 by lia.
  replace (sp - 112 + 24) with (sp - 112 + 24) by lia.
  iDestruct (arrayList_uninit_join with "Hscratch H") as "H"; [lia|lia|].
  replace (24 + 88) with 112 by lia.
  assert (Ha : sp - 112 = sp - 112 - 16 + 16) by lia. iEval (rewrite Ha) in "H".
  iDestruct (arrayList_uninit_join with "Hcallee H") as "H"; [lia|lia|].
  replace (sp - 112 - 16) with (sp - (112 + 16)) by lia. replace (16 + 112) with (112 + 16) by lia.
  iExact "H".
Qed.

Lemma ensure_x2_restore (sp : bv 64) :
  bv_add (bv_add sp (BV 64 18446744073709551504)) (BV 64 112) = sp.
Proof. bv_solve. Qed.

Lemma keysEnsureCapacity_end_bridge_slot0 `{!islaG Sigma} `{!threadG}
    (base : EnsureCapacityArgs) (returnAddress : Z) :
  ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 {| ensureBase := base |} returnAddress ⊢
  keysEnsureCapacityPost base returnAddress.
Proof.
  rewrite /ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 /keysEnsureCapacityPost.
  iIntros "(%x5 & %x6 & %x7 & %x13 & %x14 & %x15 & %x16 & %x17 & %x28 & %x29 & %x30 & %x31 & Hsys & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hhdr & Hitems & Htail & Hblock & Halloc & Hvt & Hheap & Hscr & Hscratch & W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Hcallee & %Hdom & %Hmod & %Hcap & _)".
  destruct Hdom as [Hret Hwf]. cbn [ensureBase] in *.
  pose proof Hwf as Hwf'. unfold ensureBlockArgsWellFormed, ensureBlockList in Hwf'. cbn [ensureBase] in Hwf'.
  destruct Hwf' as (Hlen & Hcapr & _ & _ & _ & _ & Hd & _).
  pose proof (keysEnsureCapacity_stack_bound base Hd) as Hsp.
  destruct Hcap as [_ Hcap].
  assert (Hc' : bv_unsigned (Z_to_bv 64 (arrayListCapacity (ensureList base))) = arrayListCapacity (ensureList base)).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. }
  rewrite Hc' in Hcap.
  iExists {| ensureKind := arrayListSuccess; ensureListAfter := ensureList base |}.
  iSplit.
  { iPureIntro. cbn. split; [exact Hret|]. split; [exact Hd|].
    unfold keysEnsureCapacityAllows. cbn. split; [apply Hd|].
    rewrite (proj2 (Z.leb_le _ _)); [|lia]. split; reflexivity. }
  rewrite /keysEnsureCapacityExit /keysEnsureCapacityScratchAfter. cbn [ensureKind ensureListAfter].
  rewrite (proj2 (Z.leb_le _ _)); [|lia].
  iExists x5, x6, x7, (BV 64 0), (ensureAllocatorPointer base), (ensureRequested base), x13, x14, x15, x16, x17, x28, x29, x30, x31.
  rewrite ensure_x2_restore arrayListSavedRegisters_unfold arrayListBuffer_unfold altFlAllocatorObject_unfold altFlVtable_unfold.
  unfold ensureBlockList; cbn [ensureBase].
  ensure_frame_addresses Hsp.
  iDestruct (ensure_frame_close with "Hcallee Hscratch W24 W32 W40 W48 W56 W64 W72 W80 W88 W96 W104") as "Hframe".
  iFrame. iPureIntro. split; reflexivity.
Qed.

Lemma ensure_scratch_close `{!islaG Sigma} `{!threadG} (a : Z) (b : bv 8) :
  a ↦ₘ? 16 -∗ (a + 16) ↦ₘ∗ [b] -∗ (a + 17) ↦ₘ? 7 -∗ a ↦ₘ? 24.
Proof.
  iIntros "H0 H1 H2".
  iDestruct (arrayList_bytes_uninit with "H1") as "H1". cbn [length Z.of_nat].
  iDestruct (arrayList_uninit_join with "H0 H1") as "H"; [lia|lia|].
  replace (a + 17) with (a + (16 + 1)) by lia.
  iDestruct (arrayList_uninit_join with "H H2") as "H"; [lia|lia|].
  replace (16 + 1 + 7) with 24 by lia. iExact "H".
Qed.

Lemma keysEnsureCapacity_end_bridge_slot1 `{!islaG Sigma} `{!threadG}
    (base : EnsureCapacityArgs) (returnAddress : Z) :
  ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 {| ensureBase := base |} returnAddress ⊢
  keysEnsureCapacityPost base returnAddress.
Proof.
  rewrite /ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 /keysEnsureCapacityPost.
  iIntros "(%x5 & %x6 & %x7 & %x11 & %x12 & %x13 & %x14 & %x15 & %x16 & %x17 & %x28 & %x29 & %x30 & %x31 & Hsys & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hhdr & Hitems & Htail & Hblock & Halloc & Hvt & Hheap & Hscr & Hs0 & Hs1 & Hs2 & W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Hcallee & %Hdom & %Hmod & %Hlt & _)".
  destruct Hdom as [Hret Hwf]. cbn [ensureBase] in *.
  pose proof Hwf as Hwf'. unfold ensureBlockArgsWellFormed, ensureBlockList in Hwf'. cbn [ensureBase] in Hwf'.
  destruct Hwf' as (Hlen & Hcapr & _ & _ & _ & _ & Hd & _).
  pose proof (keysEnsureCapacity_stack_bound base Hd) as Hsp.
  destruct Hlt as [_ Hlt].
  assert (Hc' : bv_unsigned (Z_to_bv 64 (arrayListCapacity (ensureList base))) = arrayListCapacity (ensureList base)).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. }
  rewrite Hc' in Hlt.
  iExists {| ensureKind := arrayListOutOfMemory; ensureListAfter := ensureList base |}.
  iSplit.
  { iPureIntro. cbn. split; [exact Hret|]. split; [exact Hd|].
    unfold keysEnsureCapacityAllows. cbn. split; [apply Hd|].
    rewrite (proj2 (Z.leb_gt _ _)); [|lia]. reflexivity. }
  rewrite /keysEnsureCapacityExit /keysEnsureCapacityScratchAfter. cbn [ensureKind ensureListAfter].
  rewrite (proj2 (Z.leb_gt _ _)); [|lia].
  iExists x5, x6, x7, (BV 64 2), x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  rewrite ensure_x2_restore arrayListSavedRegisters_unfold arrayListBuffer_unfold altFlAllocatorObject_unfold altFlVtable_unfold.
  unfold ensureBlockList; cbn [ensureBase].
  ensure_frame_addresses Hsp.
  iDestruct (ensure_scratch_close with "Hs0 Hs1 Hs2") as "Hscratch".
  iDestruct (ensure_frame_close with "Hcallee Hscratch W24 W32 W40 W48 W56 W64 W72 W80 W88 W96 W104") as "Hframe".
  iFrame. iPureIntro. split; reflexivity.
Qed.

(* ---- Composition over the block table. ---- *)

Lemma ensure_body_weaken `{!islaG Sigma} `{!threadG} (a : Z) (P : iProp Sigma) :
  instr_body a (P ∗ True)%I -∗ instr_body a P.
Proof. iIntros "H". iApply (instr_pre_wand with "H"); [done|done|]. iIntros "$". Qed.

(* A return slot: its caller is used at K = emp, and K (the contract
   postcondition) gives the caller's return-package premise. *)
Lemma ensure_return_slot `{!islaG Sigma} `{!threadG} (a : Z) (F Kc : iProp Sigma) :
  (Kc -∗ instr_body a ((F ∗ emp) ∗ True)%I) -∗ instr_body a (F ∗ Kc)%I.
Proof.
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "H [HF HK]". iApply ("H" with "HK"). by iFrame.
Qed.

(* reg_col stays folded while the resources are framed. *)
#[local] Typeclasses Opaque reg_col.

(* The membership of a slot: address and state both match; the index is
   found syntactically (no unification against the other entries). *)
Ltac ensure_index entry entries :=
  lazymatch entries with
  | entry :: _ => constr:(0%nat)
  | _ :: ?rest => let n := ensure_index entry rest in constr:(S n)
  end.
Ltac ensure_member :=
  lazymatch goal with
  | |- ?entry ∈ ?entries =>
      let n := ensure_index entry entries in
      exact (elem_of_list_lookup_2 entries n entry eq_refl)
  end.

(* A premise is chosen by its address: callee specs by their symbols, a
   successor by table lookup; a return premise (address returnAddress, a
   variable) is no table slot and fails at once. *)
Ltac ensure_premise :=
  lazymatch goal with
  | |- environments.envs_entails _ (instr_pre ?a _) =>
      tryif is_var a then fail else
      tryif (let s := constr:(sym_alt_fl_alloc_alloc) in constr_eq a s) then iExact "Halloc" else
      tryif (let s := constr:(sym_alt_fl_alloc_remap) in constr_eq a s) then iExact "Hremap" else
      tryif (let s := constr:(sym_alt_fl_alloc_free) in constr_eq a s) then iExact "Hfree" else
      tryif (let s := constr:(sym_memcpy) in constr_eq a s) then iExact "Hmemcpy" else
      solve [ iApply (block_table_pre_lookup with "Htab");
              unfold keysEnsureCapacityBlockTable; cbn [block_table_entries];
              ensure_member ]
  | |- _ => iExact "Hsel"
  end.

(* The return premise of a return package from the contract continuation:
   the end bridge of the package (chosen by its name) gives the contract exit. *)
Ltac ensure_exit_premise Hslot2 H :=
  iEval (rewrite /keysEnsureCapacityContinuation) in H;
  iApply (instr_pre_wand with H); [done|done|];
  unfold ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot0,
    ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot1,
    ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot2;
  iIntros "[Hexit _]";
  lazymatch iTypeOf (INamed "Hexit") with
  | Some (_, @ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot0_ForwardA0N0 _ _ _ _ _) =>
      iApply (keysEnsureCapacity_end_bridge_slot0 with "Hexit")
  | Some (_, @ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0 _ _ _ _ _) =>
      iApply (keysEnsureCapacity_end_bridge_slot1 with "Hexit")
  | Some (_, @ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 _ _ _ _ _) =>
      iApply (Hslot2 with "Hexit")
  end.

Ltac ensure_slot Hslot2 :=
  iIntros "#Htab";
  iPoseProof (block_table_pre_code with "Htab") as "#Hcode";
  iEval (unfold keysEnsureCapacityBlockTable; cbn [block_table_code];
         unfold keysEnsureCapacityTableCode) in "Hcode";
  iDestruct "Hcode" as "(Hsel & Halloc & Hremap & Hfree & Hmemcpy)";
  lazymatch goal with
  | |- environments.envs_entails _ (instr_body ?address (?entry _ _ _)) =>
      lazymatch goal with
      | H : keysEnsureCapacityBlockAt address entry _ |- _ =>
          let statement := fresh "Hstatement" in
          pose proof H as statement; unfold keysEnsureCapacityBlockAt in statement;
          first
          [ iApply ensure_body_weaken; iApply statement; ensure_premise
          | iApply ensure_return_slot; iIntros "Hret";
            iApply (statement with "[Hret]");
            [ ensure_exit_premise Hslot2 "Hret" | ensure_premise .. ] ]
      end
  end.

Ltac ensure_block_statements Sigma Hopen :=
  pose proof keysEnsureCapacityClosedBlocks as Hclosed;
  destruct Hclosed; destruct Hopen;
  repeat match goal with
  | H : forall _ : gFunctors, _ |- _ => specialize (H Sigma _ _)
  end.

(* The growth exit (return slot 2), stated as a premise until its return
   package owns the new buffer's tail (memcpy return seed). *)
Definition KeysEnsureCapacitySlot2Bridge : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG) (base : EnsureCapacityArgs) (returnAddress : Z),
    ZesuSsz.Generated.KeysEnsureCapacity.FP301.FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0 {| ensureBase := base |} returnAddress ⊢
    keysEnsureCapacityPost base returnAddress.

Lemma keysEnsureCapacity_entry_body `{!islaG Sigma} `{!threadG} :
  KeysEnsureCapacityOpenBlocks -> KeysEnsureCapacitySlot2Bridge ->
  forall (base : EnsureCapacityArgs) (returnAddress : Z),
  ⊢ □ keysEnsureCapacityTableCode -∗
    instr_body sym_array_list_Aligned_32_u8_null_ensureTotalCapacity
      (ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0000Entries.fp_machineAt0000 {| ensureBase := base |} returnAddress
        (keysEnsureCapacityContinuation {| ensureBase := base |} returnAddress)).
Proof.
  intros Hopen Hslot2 base returnAddress.
  pose proof (Hslot2 Sigma _ _ base returnAddress) as Hslot2'.
  ensure_block_statements Sigma Hopen.
  iIntros "#Htop".
  iApply (block_table_body (keysEnsureCapacityBlockTable {| ensureBase := base |} returnAddress)).
  { unfold keysEnsureCapacityBlockTable; cbn [block_table_entries]. ensure_member. }
  { iModIntro. iExact "Htop". }
  iModIntro. iIntros (address state Hin).
  unfold keysEnsureCapacityBlockTable in Hin; cbn [block_table_entries] in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]).
  all: try (apply elem_of_nil in Hin as []).
  all: injection Hin as Haddress Hstate; subst address state.
  all: ensure_slot Hslot2'.
Qed.

(* ---- The theorem, from the open blocks and the growth exit. ---- *)
Theorem keysEnsureCapacityComplianceFrom :
  KeysEnsureCapacityOpenBlocks -> KeysEnsureCapacitySlot2Bridge ->
  KeysEnsureCapacityContractCorrect.
Proof.
  intros Hopen Hslot2 returnAddress Sigma HG HT.
  change (⊢ keysEnsureCapacityContractCode -∗ ∀ base : EnsureCapacityArgs,
    instr_body sym_array_list_Aligned_32_u8_null_ensureTotalCapacity
      ((⌜bv_unsigned (ensureReturnAddress base) = returnAddress⌝ ∗ keysEnsureCapacityEntry base) ∗
       instr_pre returnAddress (keysEnsureCapacityPost base returnAddress)))%I.
  iIntros "Hcode" (base).
  rewrite /keysEnsureCapacityContractCode /altFlAllocatorPremises /altFlAllocCallPremise
    /altFlRemapCallPremise /altFlFreeCallPremise /ziskMemcpyCallPremise.
  iDestruct "Hcode" as "(#Hsel & (#Halloc & #Hremap & #Hfree) & #Hmemcpy)".
  iPoseProof (keysEnsureCapacity_entry_body Hopen Hslot2 base returnAddress with "[]") as "Hbody".
  { iModIntro. unfold keysEnsureCapacityTableCode. iFrame "#". }
  iApply (instr_pre_wand with "Hbody"); [done|done|].
  iIntros "[Hentry Hexit]".
  rewrite /ZesuSsz.Generated.KeysEnsureCapacity.FP301.Pilot0000Entries.fp_machineAt0000 /keysEnsureCapacityContinuation.
  iSplitL "Hentry"; [by iApply keysEnsureCapacity_start_bridge|].
  iExact "Hexit".
Qed.
