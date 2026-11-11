(* The decodeItem compliance theorem over the 24 generated block proofs.
   The block table and the caller statements come from the design table
   (ZesuSsz/Evidence/decode_item_block_design.json); each slot is closed by the
   generated caller lemma whose conclusion matches it (one generic slot tactic).
   This module adds the theorem only; it does not replace the production
   compliance theorem in DecodeItemCompliance.v. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Automation2.BlockTable.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6960Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6974Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot697cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot698cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69a4Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69b0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69d8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69e0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69e8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a00Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a08Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a14Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a24Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a38Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a40Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a64Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a6cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6aa8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ab4Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ac4Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ad8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6ae0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6b08Entries.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6960.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6974.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller697c.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller698c.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller69a4.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller69b0.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller69d8.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller69e0.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller69e8.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6a00.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6a08.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6a14.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6a24.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6a38.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6a40.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6a64.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6a6c.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6a78.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6aa8.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6ab4.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6ac4.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6ad8.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6ae0.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller6b08.
Local Open Scope Z_scope.


(* The contract continuation, rephrased at the return package with an empty frame.
   Every entry carries it as K; a return block receives it as its return premise. *)
Local Notation fp301Continuation args returnAddress :=
  (instr_pre returnAddress (ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.fp_machineReturn args returnAddress emp)).

Definition fp301Table `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) : blockTable Sigma := {|
  block_table_code := decodeItemSelectedCode;
  block_table_entries := [
    (0x800d6960, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6960Entries.fp_machineAt6960 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6974, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6974Entries.fp_machineAt6974 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d697c, (ZesuSsz.Generated.DecodeItem.FP301.Pilot697cEntries.fp_machineAt697c args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d698c, (ZesuSsz.Generated.DecodeItem.FP301.Pilot698cEntries.fp_machineAt698c args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d69a4, (ZesuSsz.Generated.DecodeItem.FP301.Pilot69a4Entries.fp_machineAt69a4 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d69b0, (ZesuSsz.Generated.DecodeItem.FP301.Pilot69b0Entries.fp_machineAt69b0 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d69d8, (ZesuSsz.Generated.DecodeItem.FP301.Pilot69d8Entries.fp_machineAt69d8 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d69e0, (ZesuSsz.Generated.DecodeItem.FP301.Pilot69e0Entries.fp_machineAt69e0 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d69e8, (ZesuSsz.Generated.DecodeItem.FP301.Pilot69e8Entries.fp_machineAt69e8 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a00, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a00Entries.fp_machineAt6a00 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a08, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a08Entries.fp_machineAt6a08 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a14, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a14Entries.fp_machineAt6a14 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a24, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a24Entries.fp_machineAt6a24 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a38, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a38Entries.fp_machineAt6a38 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a40, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a40Entries.fp_machineAt6a40 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a64, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a64Entries.fp_machineAt6a64 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a6c, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a6cEntries.fp_machineAt6a6c args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a78, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Entries.fp_machineAt6a78 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6aa8, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6aa8Entries.fp_machineAt6aa8 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6ab4, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6ab4Entries.fp_machineAt6ab4 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6ac4, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6ac4Entries.fp_machineAt6ac4 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6ad8, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6ad8Entries.fp_machineAt6ad8 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6ae0, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6ae0Entries.fp_machineAt6ae0 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6b08, (ZesuSsz.Generated.DecodeItem.FP301.Pilot6b08Entries.fp_machineAt6b08 args returnAddress (fp301Continuation args returnAddress))%I)
  ] |}.

(* ---- Infrastructure (hand-written once; no step names a block). ---- *)

Lemma fp301_body_weaken `{!islaG Sigma} `{!threadG} (a : Z) (P : iProp Sigma) :
  instr_body a (P ∗ True)%I -∗ instr_body a P.
Proof. iIntros "H". iApply (instr_pre_wand with "H"); [done|done|]. iIntros "$". Qed.

(* A return block's caller takes its return premise outside the body; the
   entry state supplies it as K. *)
Lemma fp301_return_slot `{!islaG Sigma} `{!threadG} (a : Z) (F Kc : iProp Sigma) :
  (Kc -∗ instr_body a ((F ∗ emp) ∗ True)%I) -∗ instr_body a (F ∗ Kc)%I.
Proof.
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "H [HF HK]". iApply ("H" with "HK"). by iFrame.
Qed.

Lemma fp301_byte_array_to_uninit `{!islaG Sigma} `{!threadG} (a : Z) (l : list (bv 8)) (n : Z) :
  Z.of_nat (length l) = n -> a ↦ₘ∗ l -∗ a ↦ₘ? n.
Proof.
  intros <-.
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

Ltac fp301_member :=
  repeat lazymatch goal with
  | |- (?a, _) ∈ (?a, _) :: _ => apply elem_of_list_here
  | |- _ ∈ _ :: _ => apply elem_of_list_further
  end.

Ltac fp301_premise :=
  first [ iExact "HtabCode"
        | solve [ iApply (block_table_pre_lookup with "Htab"); simpl; fp301_member ] ].

(* The generic slot step: the block lemma whose conclusion matches the slot.
   A successor premise comes from the table and the code from the table code;
   a return premise comes from the K in the slot's own entry state. *)
Ltac fp301_slot :=
  iIntros "#Htab";
  iPoseProof (block_table_pre_code with "Htab") as "#HtabCode";
  first
  [ iApply fp301_body_weaken;
    match goal with
    | H : forall (_ : DecodeItemArgs) (_ : Z) (_ : iProp _), bi_emp_valid _ |- _ =>
        iApply H; fp301_premise
    end
  | iApply fp301_return_slot; iIntros "Hret";
    match goal with
    | H : forall (_ : DecodeItemArgs) (_ : Z) (_ : iProp _), bi_emp_valid _ |- _ =>
        iApply (H with "Hret HtabCode")
    end ].

(* The 24 generated block proofs at this Sigma, with the caller entry unfolded
   (the callers make it typeclass-opaque); the slot tactic picks the proof
   whose conclusion matches the slot. *)
Ltac fp301_block_proofs Sigma :=
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6960.DesignedBoundary_800d6960 Sigma _ _) as Fp301Block_800d6960;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6960.DesignedEntry_800d6960 in Fp301Block_800d6960;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6974.DesignedBoundary_800d6974 Sigma _ _) as Fp301Block_800d6974;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6974.DesignedEntry_800d6974 in Fp301Block_800d6974;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller697c.DesignedBoundary_800d697c Sigma _ _) as Fp301Block_800d697c;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller697c.DesignedEntry_800d697c in Fp301Block_800d697c;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller698c.DesignedBoundary_800d698c Sigma _ _) as Fp301Block_800d698c;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller698c.DesignedEntry_800d698c in Fp301Block_800d698c;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller69a4.DesignedBoundary_800d69a4 Sigma _ _) as Fp301Block_800d69a4;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller69a4.DesignedEntry_800d69a4 in Fp301Block_800d69a4;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller69b0.DesignedBoundary_800d69b0 Sigma _ _) as Fp301Block_800d69b0;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller69b0.DesignedEntry_800d69b0 in Fp301Block_800d69b0;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller69d8.DesignedBoundary_800d69d8 Sigma _ _) as Fp301Block_800d69d8;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller69d8.DesignedEntry_800d69d8 in Fp301Block_800d69d8;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller69e0.DesignedBoundary_800d69e0 Sigma _ _) as Fp301Block_800d69e0;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller69e0.DesignedEntry_800d69e0 in Fp301Block_800d69e0;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller69e8.DesignedBoundary_800d69e8 Sigma _ _) as Fp301Block_800d69e8;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller69e8.DesignedEntry_800d69e8 in Fp301Block_800d69e8;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6a00.DesignedBoundary_800d6a00 Sigma _ _) as Fp301Block_800d6a00;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6a00.DesignedEntry_800d6a00 in Fp301Block_800d6a00;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6a08.DesignedBoundary_800d6a08 Sigma _ _) as Fp301Block_800d6a08;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6a08.DesignedEntry_800d6a08 in Fp301Block_800d6a08;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6a14.DesignedBoundary_800d6a14 Sigma _ _) as Fp301Block_800d6a14;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6a14.DesignedEntry_800d6a14 in Fp301Block_800d6a14;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6a24.DesignedBoundary_800d6a24 Sigma _ _) as Fp301Block_800d6a24;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6a24.DesignedEntry_800d6a24 in Fp301Block_800d6a24;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6a38.DesignedBoundary_800d6a38 Sigma _ _) as Fp301Block_800d6a38;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6a38.DesignedEntry_800d6a38 in Fp301Block_800d6a38;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6a40.DesignedBoundary_800d6a40 Sigma _ _) as Fp301Block_800d6a40;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6a40.DesignedEntry_800d6a40 in Fp301Block_800d6a40;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6a64.DesignedBoundary_800d6a64 Sigma _ _) as Fp301Block_800d6a64;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6a64.DesignedEntry_800d6a64 in Fp301Block_800d6a64;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6a6c.DesignedBoundary_800d6a6c Sigma _ _) as Fp301Block_800d6a6c;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6a6c.DesignedEntry_800d6a6c in Fp301Block_800d6a6c;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6a78.DesignedBoundary_800d6a78 Sigma _ _) as Fp301Block_800d6a78;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6a78.DesignedEntry_800d6a78 in Fp301Block_800d6a78;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6aa8.DesignedBoundary_800d6aa8 Sigma _ _) as Fp301Block_800d6aa8;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6aa8.DesignedEntry_800d6aa8 in Fp301Block_800d6aa8;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6ab4.DesignedBoundary_800d6ab4 Sigma _ _) as Fp301Block_800d6ab4;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6ab4.DesignedEntry_800d6ab4 in Fp301Block_800d6ab4;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6ac4.DesignedBoundary_800d6ac4 Sigma _ _) as Fp301Block_800d6ac4;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6ac4.DesignedEntry_800d6ac4 in Fp301Block_800d6ac4;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6ad8.DesignedBoundary_800d6ad8 Sigma _ _) as Fp301Block_800d6ad8;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6ad8.DesignedEntry_800d6ad8 in Fp301Block_800d6ad8;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6ae0.DesignedBoundary_800d6ae0 Sigma _ _) as Fp301Block_800d6ae0;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6ae0.DesignedEntry_800d6ae0 in Fp301Block_800d6ae0;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller6b08.DesignedBoundary_800d6b08 Sigma _ _) as Fp301Block_800d6b08;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller6b08.DesignedEntry_800d6b08 in Fp301Block_800d6b08.

(* ---- Composition over the block table. ---- *)
Lemma fp301_decodeItem_body `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) :
  ⊢ □ decodeItemSelectedCode -∗
    instr_body 0x800d6960 (ZesuSsz.Generated.DecodeItem.FP301.Pilot6960Entries.fp_machineAt6960 args returnAddress
      (fp301Continuation args returnAddress)).
Proof.
  fp301_block_proofs Sigma.
  iIntros "#Hsel".
  iApply (block_table_body (fp301Table args returnAddress)).
  { simpl. fp301_member. }
  { iModIntro. iExact "Hsel". }
  iModIntro. iIntros (address state Hin). simpl in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]).
  all: try (apply elem_of_nil in Hin as []).
  all: injection Hin as Haddress Hstate; subst address state.
  all: fp301_slot.
Qed.

(* ---- End bridge (gap report item (d)). ---- *)
Lemma fp301_end_bridge `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.fp_machineReturn args returnAddress emp ⊢
  ∃ after : DecodeItemOutcome,
    ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
      DecodeMeaningModuloKnownBugs args after⌝ ∗
    decodeItemExitResourcesRegisters args after.
Proof.
  intros Hdomain.
  rewrite /ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.fp_machineReturn.
  iIntros "[(%a3 & %a4 & %a5 & %a6 & %x12 & %x2 & %x8 & %x11 & %after & Hsys & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & H1 & H8 & Hin & Hout & Hstack & %Hsp & %Hfp & %Hlen & %Hmeaning & _) _]".
  iExists after. iSplit; [iPureIntro; split; assumption|].
  assert (Hx2 : x2 = Z_to_bv 64 (decodeItemStackPointer args))
    by (rewrite <- Hsp; by rewrite Z_to_bv_bv_unsigned).
  subst x2 x8.
  iDestruct (fp301_byte_array_to_uninit _ _ 16 with "Hstack") as "Hstack"; try reflexivity.
  rewrite /decodeItemExitResourcesRegisters /decodeItemExitResources /decodeItemReturnedCallerRegisters.
  iFrame "Hsys H2 H1 H8 Hin Hout Hstack H10 H11 H12 H13 H14 H15 H16".
Qed.

(* ---- Start bridge (gap report item (c)), keeping the domain fact. ---- *)
Lemma fp301_start_bridge `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) :
  decodeItemEntryResources (decodeItemDomainAt returnAddress decodeItemC1BDomain) args ⊢
  ZesuSsz.Generated.DecodeItem.FP301.Pilot6960Entries.fp_machineAt6960_ForwardA0N0 args returnAddress ∗
  ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args⌝.
Proof.
  iIntros "(%a3 & %a4 & %a5 & %a6 & Hsys & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & H1 & H8 & Hin & Hout & Hstack & %Hdomain & _)".
  iSplit; [|done].
  iExists a3, a4, a5, a6, (BV 64 0), (BV 64 0), (BV 64 0).
  iFrame. iSplit; [done|]. iSplit; [done|]. iPureIntro. split; reflexivity.
Qed.

(* ---- The statement decodeItemSelectedComplianceRegisters consumes, at one Sigma. ---- *)
Lemma fp301_registers_body `{!islaG Sigma} `{!threadG} (returnAddress : Z) :
  ⊢ decodeItemSelectedCode -∗ ∀ args : DecodeItemArgs,
    instr_body decodeItemEntry
      (decodeItemEntryResources (decodeItemDomainAt returnAddress decodeItemC1BDomain) args ∗
       instr_pre returnAddress (∃ after : DecodeItemOutcome,
         ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
           DecodeMeaningModuloKnownBugs args after⌝ ∗
         decodeItemExitResourcesRegisters args after)).
Proof.
  iIntros "#Hsel" (args).
  iPoseProof (fp301_decodeItem_body args returnAddress with "Hsel") as "Hbody".
  iApply (instr_pre_wand with "Hbody"); [done|done|].
  iIntros "[Hentry Hexit]".
  iDestruct (fp301_start_bridge with "Hentry") as "[Hforward %Hdomain]".
  rewrite /ZesuSsz.Generated.DecodeItem.FP301.Pilot6960Entries.fp_machineAt6960.
  iFrame "Hforward".
  iApply (instr_pre_wand with "Hexit"); [done|done|].
  iIntros "Hreturn". by iApply (fp301_end_bridge with "Hreturn").
Qed.


(* ---- The registers statement and its weakening to the reviewed model. ---- *)
Lemma decodeItemGeneratedComplianceRegisters :
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModelRegisters returnAddress).
Proof.
  intros returnAddress Sigma HG HT.
  change (⊢ decodeItemSelectedCode -∗ ∀ args : DecodeItemArgs,
    instr_body decodeItemEntry
      (decodeItemEntryResources (decodeItemDomainAt returnAddress decodeItemC1BDomain) args ∗
       instr_pre returnAddress (∃ after : DecodeItemOutcome,
         ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
           DecodeMeaningModuloKnownBugs args after⌝ ∗
         decodeItemExitResourcesRegisters args after)))%I.
  exact (@fp301_registers_body Sigma HG HT returnAddress).
Qed.

Lemma fp301_register_exit_weakens `{!islaG Sigma} `{!threadG} args after :
  decodeItemExitResourcesRegisters args after ⊢ decodeItemExitResources args after.
Proof.
  rewrite /decodeItemExitResourcesRegisters.
  iIntros "[Hbase _]". iExact "Hbase".
Qed.

Lemma decodeItemGeneratedCompliance :
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModel returnAddress).
Proof.
  intros returnAddress Sigma HG HT.
  pose proof (decodeItemGeneratedComplianceRegisters returnAddress Sigma HG HT) as Hnative.
  unfold IslarisContractSpec, decodeItemSelectedModelRegisters, decodeItemResourcesRegisters in Hnative; cbn in Hnative.
  change (⊢ decodeItemSelectedCode -∗ ∀ args : DecodeItemArgs,
    instr_body decodeItemEntry
      (decodeItemEntryResources (decodeItemDomainAt returnAddress decodeItemC1BDomain) args ∗
       instr_pre returnAddress (∃ after : DecodeItemOutcome,
         ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
           DecodeMeaningModuloKnownBugs args after⌝ ∗ decodeItemExitResources args after)))%I.
  iIntros "Hcode" (args).
  iPoseProof (Hnative with "Hcode") as "Hbody".
  iSpecialize ("Hbody" $! args).
  iApply (instr_pre_wand with "Hbody []"); [done|done|].
  iIntros "[Hentry Hreturn]". iFrame "Hentry".
  iApply (instr_pre_wand with "Hreturn []"); [done|done|].
  iIntros "Hafter". iDestruct "Hafter" as (after) "[%Hallowed Hexit]". iExists after. iFrame "%".
  iApply (fp301_register_exit_weakens with "Hexit").
Qed.
