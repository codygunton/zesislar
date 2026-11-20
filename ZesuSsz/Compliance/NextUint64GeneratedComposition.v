(* nextUint64 compliance from its block obligations.
   The composition runs over the generated block table
   (NextUint64BlockObligations.v, from tools/block/render_open_blocks.py).
   A slot is closed by the block statement tagged with its address and entry
   constant: a compiled caller lemma (NextUint64ClosedBlocks) or a field of
   NextUint64OpenBlocks (now empty). Every entry carries the generated return entry as K
   (nextUint64Continuation); the return block 0x0070 consumes it, and the end
   bridge turns the return entry into the contract exit. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Automation2.BlockTable.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Contracts.NextUint64Contract.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Interfaces.DecodeItemCorrect.
Require Import ZesuSsz.Compliance.NextUint64CompositionBoundary.
Require Import ZesuSsz.Compliance.NextUint64BlockObligations.
Require ZesuSsz.Generated.NextUint64.FP301.Pilot0000Entries.
Require ZesuSsz.Generated.NextUint64.FP301.FunctionReturnEntries.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Typeclasses Transparent nextUint64SelectedCode decodeItemSelectedCode.

(* ---- Infrastructure (no step names a block). ---- *)

Lemma nextUint64_body_weaken `{!islaG Sigma} `{!threadG} (a : Z) (P : iProp Sigma) :
  instr_body a (P ∗ True)%I -∗ instr_body a P.
Proof. iIntros "H". iApply (instr_pre_wand with "H"); [done|done|]. iIntros "$". Qed.

(* The return block takes its return premise from the K of its own entry. *)
Lemma nextUint64_return_slot `{!islaG Sigma} `{!threadG} (a : Z) (F Kc : iProp Sigma) :
  (Kc -∗ instr_body a ((F ∗ emp) ∗ True)%I) -∗ instr_body a (F ∗ Kc)%I.
Proof.
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "H [HF HK]". iApply ("H" with "HK"). by iFrame.
Qed.

Lemma nextUint64_decodeItem_boxed `{!islaG Sigma} `{!threadG} :
  decodeItemSelectedCode -∗ □ instr_pre decodeItemEntry decodeItemCallSpec2.
Proof.
  iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply decodeItemCallSpec2_correct. iExact "Hcode".
Qed.

Ltac nextUint64_member :=
  repeat lazymatch goal with
  | |- ?entry ∈ ?entry :: _ => apply elem_of_list_here
  | |- _ ∈ _ :: _ => apply elem_of_list_further
  end.

(* A premise is chosen by its address: decodeItemEntry is the callee spec. A
   table premise either closes by lookup or fails, so that the return block
   falls through to its own slot step. *)
Ltac nextUint64_premise :=
  lazymatch goal with
  | |- environments.envs_entails _ (instr_pre 0x800d6960 _) => iExact "Hdi"
  | |- environments.envs_entails _ (instr_pre _ _) =>
      solve [ iApply (block_table_pre_lookup with "Htab");
              unfold nextUint64BlockTable; cbn [block_table_entries];
              nextUint64_member ]
  | |- _ => iExact "Hsel"
  end.

Ltac nextUint64_slot :=
  iIntros "#Htab";
  iPoseProof (block_table_pre_code with "Htab") as "#Hcode";
  iEval (unfold nextUint64BlockTable; cbn [block_table_code];
         unfold nextUint64TableCode) in "Hcode";
  iDestruct "Hcode" as "(Hsel & Hdi)";
  lazymatch goal with
  | |- environments.envs_entails _ (instr_body ?address (?entry _ _ _)) =>
      lazymatch goal with
      | H : nextUint64BlockAt address entry _ |- _ =>
          let statement := fresh "Hstatement" in
          pose proof H as statement; unfold nextUint64BlockAt in statement;
          first
          [ iApply nextUint64_body_weaken; iApply statement; nextUint64_premise
          | iApply nextUint64_return_slot; iIntros "Hret";
            iApply (statement with "Hret Hsel") ]
      end
  end.

Ltac nextUint64_block_statements Sigma Hopen :=
  pose proof nextUint64ClosedBlocks as Hclosed;
  destruct Hclosed; destruct Hopen;
  repeat match goal with
  | H : forall _ : gFunctors, _ |- _ => specialize (H Sigma _ _)
  end.

(* ---- Composition over the block table. ---- *)
Lemma nextUint64_entry_body `{!islaG Sigma} `{!threadG} :
  NextUint64OpenBlocks ->
  forall (args : NextUint64Args) (returnAddress : Z),
  ⊢ □ nextUint64TableCode -∗
    instr_body nextUint64Entry
      (ZesuSsz.Generated.NextUint64.FP301.Pilot0000Entries.fp_machineAt0000 args returnAddress
        (nextUint64Continuation args returnAddress)).
Proof.
  intros Hopen args returnAddress.
  nextUint64_block_statements Sigma Hopen.
  iIntros "#Htop".
  iApply (block_table_body (nextUint64BlockTable args returnAddress)).
  { unfold nextUint64BlockTable; cbn [block_table_entries]. nextUint64_member. }
  { iModIntro. iExact "Htop". }
  iModIntro. iIntros (address state Hin).
  unfold nextUint64BlockTable in Hin; cbn [block_table_entries] in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]).
  all: try (apply elem_of_nil in Hin as []).
  all: injection Hin as Haddress Hstate; subst address state.
  all: nextUint64_slot.
Qed.

(* ---- Bridges between the contract boundary and the generated entries. ---- *)

Lemma nextUint64_frame_address (sp : Z) (c d : bv 64) :
  112 <= sp < 2 ^ 64 -> bv_unsigned c = 18446744073709551520 -> bv_unsigned d < 96 ->
  bv_unsigned (bv_add (bv_add (Z_to_bv 64 sp) c) d) = sp - 96 + bv_unsigned d.
Proof.
  intros Hsp Hc Hd. pose proof (bv_unsigned_in_range _ d) as Hdr. unfold bv_modulus in Hdr.
  rewrite !bv_add_unsigned !Z_to_bv_unsigned Hc. unfold bv_wrap, bv_modulus in *.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in *.
  rewrite (Z.mod_small sp); lia.
Qed.

Lemma nextUint64_frame_word `{!islaG Sigma} `{!threadG} (a : Z) :
  a ↦ₘ? 8 -∗ ∃ w : bv 64, a ↦ₘ w.
Proof.
  iIntros "H". iDestruct (mem_mapsto_uninit_to_mapsto with "H") as (n' b ->) "H".
  iExists b. iExact "H".
Qed.

Lemma nextUint64_stack_bound (params : NextUint64Args) :
  nextUint64BoundaryDomain params ->
  112 <= nextStackPointer (nextUint64Base params) < 2 ^ 64.
Proof.
  intros Hd. pose proof Hd as (Hl & H112 & _). unfold nextUint64EntryLayout in Hl.
  cbv zeta in Hl. destruct Hl as (_ & _ & _ & _ & _ & _ & _ & Hsp & _). lia.
Qed.

(* The caller's 96 bytes as the entry frame of block 0x0000: 48 bytes, then six
   words that the prologue saves into. *)
Lemma nextUint64_frame_open `{!islaG Sigma} `{!threadG} (sp : Z) :
  (sp - 96) ↦ₘ? 96 -∗
  (sp - 96) ↦ₘ? 48 ∗ ∃ w48 w40 w32 w24 w16 w8 : bv 64,
    (sp - 96 + 48) ↦ₘ w48 ∗ (sp - 96 + 56) ↦ₘ w40 ∗ (sp - 96 + 64) ↦ₘ w32 ∗
    (sp - 96 + 72) ↦ₘ w24 ∗ (sp - 96 + 80) ↦ₘ w16 ∗ (sp - 96 + 88) ↦ₘ w8.
Proof.
  iIntros "H".
  iDestruct (mem_mapsto_uninit_split 48 with "H") as "[$ H]"; [lia|].
  iDestruct (mem_mapsto_uninit_split 8 with "H") as "[H48 H]"; [lia|].
  iDestruct (mem_mapsto_uninit_split 8 with "H") as "[H56 H]"; [lia|].
  iDestruct (mem_mapsto_uninit_split 8 with "H") as "[H64 H]"; [lia|].
  iDestruct (mem_mapsto_uninit_split 8 with "H") as "[H72 H]"; [lia|].
  iDestruct (mem_mapsto_uninit_split 8 with "H") as "[H80 H88]"; [lia|].
  iDestruct (nextUint64_frame_word with "H48") as (w48) "H48".
  iDestruct (nextUint64_frame_word with "H56") as (w40) "H56".
  iDestruct (nextUint64_frame_word with "H64") as (w32) "H64".
  iDestruct (nextUint64_frame_word with "H72") as (w24) "H72".
  iDestruct (nextUint64_frame_word with "H80") as (w16) "H80".
  replace (96 - 48 - 8 - 8 - 8 - 8 - 8) with 8 by lia.
  iDestruct (nextUint64_frame_word with "H88") as (w8) "H88".
  iExists w48, w40, w32, w24, w16, w8.
  replace (sp - 96 + 48 + 8) with (sp - 96 + 56) by lia.
  replace (sp - 96 + 56 + 8) with (sp - 96 + 64) by lia.
  replace (sp - 96 + 64 + 8) with (sp - 96 + 72) by lia.
  replace (sp - 96 + 72 + 8) with (sp - 96 + 80) by lia.
  replace (sp - 96 + 80 + 8) with (sp - 96 + 88) by lia.
  iFrame.
Qed.

Lemma nextUint64_return_address_bound (params : NextUint64Args) :
  nextUint64BoundaryDomain params ->
  0 <= nextReturnAddress (nextUint64Base params) < 2 ^ 64 /\
  nextReturnAddress (nextUint64Base params) mod 4 = 0.
Proof.
  intros [Hl _]. unfold nextUint64EntryLayout in Hl. cbv zeta in Hl. lia.
Qed.

(* The entries write a frame address as the stack pointer plus two constants. *)
Ltac nextUint64_frame_addresses Hsp :=
  repeat match goal with
  | |- context [bv_unsigned (bv_add (bv_add (Z_to_bv 64 ?sp) ?c) ?d)] =>
      rewrite (nextUint64_frame_address sp c d Hsp); [|reflexivity|cbn; lia]
  end;
  cbn [bv_unsigned].

Lemma nextUint64_start_bridge `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (returnAddress : Z) :
  nextUint64ContractEntry returnAddress params ⊢
  ZesuSsz.Generated.NextUint64.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0 params returnAddress.
Proof.
  rewrite /nextUint64ContractEntry /nextUint64BoundaryEntry /nextUint64EntryAt800d6274 /nextUint64Registers
    /ZesuSsz.Generated.NextUint64.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0.
  iIntros "[(%x5 & %x6 & %x7 & %x10 & %x11 & %x12 & %x13 & %x14 & %x15 & %x16 & %x17 & %x28 & %x29 & %x30 & %x31 & Hsys & (H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31) & Hin & Hsl & Hres & Hst & Hcs & %Hfacts & _) [%Hret _]]".
  destruct Hfacts as (Hdomain & _ & _ & _ & _ & _ & _ & Hx10 & Hx11 & _).
  subst x10 x11.
  pose proof (nextUint64_stack_bound _ Hdomain) as Hsp.
  iDestruct (nextUint64_frame_open with "Hst") as "[Hlow (%w48 & %w40 & %w32 & %w24 & %w16 & %w8 & H48 & H56 & H64 & H72 & H80 & H88)]".
  iExists x5, x6, x7, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31.
  iExists w48, w40, w32, w24, w16, w8.
  nextUint64_frame_addresses Hsp.
  iFrame.
  pose proof (nextUint64_return_address_bound _ Hdomain) as Hra.
  iPureIntro. split_and!; [exact Hret|exact Hdomain| |].
  - rewrite Z_to_bv_unsigned bv_wrap_small; [exact (proj2 Hra)|exact (proj1 Hra)].
  - apply zesu_hist_intro.
    unfold ZesuSsz.Generated.NextUint64.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0_Hist.
    exists (BV 64 0). split; vm_compute; reflexivity.
Qed.

Lemma nextUint64_byte_array_to_uninit `{!islaG Sigma} `{!threadG} (a : Z) (l : list (bv 8)) :
  a ↦ₘ∗ l -∗ a ↦ₘ? (Z.of_nat (length l)).
Proof.
  rewrite mem_mapsto_array_eq mem_mapsto_uninit_eq.
  iIntros "(%len & %Hlen & %Hrange & Hl)".
  assert (len = 1%N) as -> by lia.
  iExists (length l). iSplit; [done|]. iSplit; [iPureIntro; lia|].
  iApply (big_sepL_impl' with "Hl"); [by rewrite length_replicate|].
  iIntros "!>" (k v u Hv Hu) "Hv".
  iDestruct (mem_mapsto_mapsto_to_uninit with "Hv") as "Hu".
  rewrite mem_mapsto_uninit_eq.
  iDestruct "Hu" as (nn Hnn Hr) "Hb".
  assert (nn = 1%nat) as -> by (cbn in Hnn; lia).
  iDestruct "Hb" as "[[%b Hb] _]". iExists b.
  replace (a + k * Z.of_N 1 + 0%nat) with (a + k) by lia. done.
Qed.

Lemma nextUint64_uninit_join `{!islaG Sigma} `{!threadG} (a m n : Z) :
  0 <= m -> 0 <= n -> a ↦ₘ? m -∗ (a + m) ↦ₘ? n -∗ a ↦ₘ? (m + n).
Proof.
  iIntros (Hm Hn) "H1 H2".
  iApply (mem_mapsto_uninit_combine m a _ (m + n) with "H1 [H2]"); [lia|].
  by replace (m + n - m) with n by lia.
Qed.

(* The return frame of block 0x0070 as the caller's 96 bytes. *)
Lemma nextUint64_frame_close `{!islaG Sigma} `{!threadG} (sp : Z) (after : list byte)
    (w48 w40 w32 w24 w16 w8 : bv 64) :
  length after = 40%nat ->
  (sp - 96) ↦ₘ? 8 -∗ (sp - 96 + 8) ↦ₘ∗ after -∗
  (sp - 96 + 48) ↦ₘ w48 -∗ (sp - 96 + 56) ↦ₘ w40 -∗ (sp - 96 + 64) ↦ₘ w32 -∗
  (sp - 96 + 72) ↦ₘ w24 -∗ (sp - 96 + 80) ↦ₘ w16 -∗ (sp - 96 + 88) ↦ₘ w8 -∗
  (sp - 96) ↦ₘ? 96.
Proof.
  iIntros (Hlen) "H0 Ha H48 H56 H64 H72 H80 H88".
  iDestruct (nextUint64_byte_array_to_uninit with "Ha") as "Ha". rewrite Hlen.
  iDestruct (mem_mapsto_mapsto_to_uninit with "H48") as "H48".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H56") as "H56".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H64") as "H64".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H72") as "H72".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H80") as "H80".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H88") as "H88".
  change (Z.of_N (64 `div` 8)) with 8. change (Z.of_nat 40) with 40.
  replace (sp - 96 + 88) with (sp - 96 + 80 + 8) by lia.
  iDestruct (nextUint64_uninit_join with "H80 H88") as "H"; [lia|lia|].
  replace (sp - 96 + 80) with (sp - 96 + 72 + 8) by lia.
  iDestruct (nextUint64_uninit_join with "H72 H") as "H"; [lia|lia|].
  replace (sp - 96 + 72) with (sp - 96 + 64 + 8) by lia.
  iDestruct (nextUint64_uninit_join with "H64 H") as "H"; [lia|lia|].
  replace (sp - 96 + 64) with (sp - 96 + 56 + 8) by lia.
  iDestruct (nextUint64_uninit_join with "H56 H") as "H"; [lia|lia|].
  replace (sp - 96 + 56) with (sp - 96 + 48 + 8) by lia.
  iDestruct (nextUint64_uninit_join with "H48 H") as "H"; [lia|lia|].
  replace (sp - 96 + 48) with (sp - 96 + 8 + 40) by lia.
  iDestruct (nextUint64_uninit_join with "Ha H") as "H"; [lia|lia|].
  iDestruct (nextUint64_uninit_join with "H0 H") as "H"; [lia|lia|].
  iExact "H".
Qed.

Lemma nextUint64_end_bridge `{!islaG Sigma} `{!threadG} (params : NextUint64Args) (returnAddress : Z) :
  ZesuSsz.Generated.NextUint64.FP301.FunctionReturnEntries.fp_machineReturn params returnAddress emp ⊢
  ∃ result : NextUint64Return,
    ⌜nextUint64ContractAllows returnAddress params result⌝ ∗
    nextUint64ContractExit params result.
Proof.
  rewrite /ZesuSsz.Generated.NextUint64.FP301.FunctionReturnEntries.fp_machineReturn
    /ZesuSsz.Generated.NextUint64.FP301.FunctionReturnEntries.fp_machineReturn_ForwardA0N0.
  iIntros "[(%c5 & %c6 & %c7 & %c15 & %c16 & %c17 & %c28 & %c29 & %c30 & %c31 & %after & %m10 & %m11 & %m12 & %m13 & %m14 & %j31 & %j32 & Hsys & H1 & H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & Hin & Hsl & Hres & H0 & Ha & H48 & H56 & H64 & H72 & H80 & H88 & Hcs & %Hra & %Hmod & %Hlen & %Hfacts) _]".
  (* The history is the last pure fact; its first conjunct names the result. *)
  repeat lazymatch type of Hfacts with
  | zesu_hist _ => fail
  | _ /\ _ => destruct Hfacts as [_ Hfacts]
  end.
  apply zesu_hist_elim in Hfacts.
  unfold ZesuSsz.Generated.NextUint64.FP301.FunctionReturnEntries.fp_machineReturn_ForwardA0N0_Hist in Hfacts.
  destruct Hfacts as (? & ? & ? & ? & ? & ? & ? & ? & (result & Hbytes & Hslice & Hroot) & _).
  subst j31 j32.
  destruct Hra as [Hret Hdomain].
  pose proof (nextUint64_stack_bound _ Hdomain) as Hsp.
  iExists result. iSplit.
  { iPureIntro. split; [exact Hret|split; [exact Hdomain|exact Hroot]]. }
  rewrite /nextUint64ContractExit /nextUint64Registers.
  iExists c5, c6, c7, m10, m11, m12, m13, m14, c15, c16, c17, c28, c29, c30, c31.
  nextUint64_frame_addresses Hsp.
  iDestruct (nextUint64_frame_close with "H0 Ha H48 H56 H64 H72 H80 H88") as "Hframe"; [exact Hlen|].
  assert (Hx2 : bv_add (bv_add (Z_to_bv 64 (nextStackPointer (nextUint64Base params)))
      (BV 64 18446744073709551520)) (BV 64 96) = Z_to_bv 64 (nextStackPointer (nextUint64Base params)))
    by bv_solve.
  rewrite Hx2.
  replace (nextStackPointer (nextUint64Base params) - 96 - 16)
    with (nextStackPointer (nextUint64Base params) - 112) by lia.
  iFrame.
Qed.

(* ---- The theorem: nextUint64 compliance; every block is closed. The contract's
   code holds decodeItem's map, which block 0x0000's call needs. ---- *)
Theorem nextUint64GeneratedCompliance :
  NextUint64ContractCorrect.
Proof.
  intros returnAddress Sigma HG HT.
  change (⊢ (nextUint64SelectedCode ∗ decodeItemSelectedCode) -∗ ∀ params : NextUint64Args,
    instr_body nextUint64Entry
      (nextUint64ContractEntry returnAddress params ∗
       instr_pre returnAddress (∃ result : NextUint64Return,
         ⌜nextUint64ContractAllows returnAddress params result⌝ ∗
         nextUint64ContractExit params result)))%I.
  iIntros "[#Hsel #Hdi]" (params).
  iPoseProof (nextUint64_decodeItem_boxed with "Hdi") as "#Hdi2".
  iPoseProof (nextUint64_entry_body nextUint64OpenBlocks params returnAddress with "[]") as "Hbody".
  { iModIntro. unfold nextUint64TableCode.
    iSplitR; [iExact "Hsel"|]. iModIntro. iExact "Hdi2". }
  iApply (instr_pre_wand with "Hbody"); [done|done|].
  iIntros "[Hentry Hexit]".
  rewrite /ZesuSsz.Generated.NextUint64.FP301.Pilot0000Entries.fp_machineAt0000 /nextUint64Continuation.
  iSplitL "Hentry"; [by iApply nextUint64_start_bridge|].
  iApply (instr_pre_wand with "Hexit"); [done|done|].
  iIntros "Hreturn". by iApply (nextUint64_end_bridge with "Hreturn").
Qed.

(* Plan step 2.2: the final nextUint64 statement. *)
Theorem nextUint64Compliance : NextUint64ContractCorrect.
Proof. exact nextUint64GeneratedCompliance. Qed.
