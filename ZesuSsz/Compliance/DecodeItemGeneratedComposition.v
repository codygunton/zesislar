(* The composition of the 24 generated block proofs over the block table.
   The block table and the caller statements come from the design table
   (ZesuSsz/Evidence/decode_item_block_design.json); each slot is closed by the
   generated caller lemma whose conclusion matches it (one generic slot tactic).
   DecodeItemComplianceGenerated.v states the compliance theorems from it. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Automation2.BlockTable.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Contracts.DecodeItemDomainRanges.
Require Import ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0000Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0014Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot001cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot002cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0044Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0050Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0078Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0080Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0088Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot00a0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot00a8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot00b4Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot00c4Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot00d8Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot00e0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0104Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot010cEntries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0118Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0148Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0154Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0164Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0178Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0180Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot01a8Entries.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0000.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0014.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller001c.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller002c.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0044.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0050.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0078.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0080.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0088.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller00a0.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller00a8.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller00b4.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller00c4.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller00d8.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller00e0.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0104.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller010c.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0118.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0148.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0154.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0164.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0178.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller0180.
Require ZesuSsz.Proofs.DecodeItem.FP301.Caller01a8.
Local Open Scope Z_scope.


(* The contract continuation, rephrased at the return package with an empty frame.
   Every entry carries it as K; a return block receives it as its return premise. *)
Local Notation fp301Continuation args returnAddress :=
  (instr_pre returnAddress (ZesuSsz.Generated.DecodeItem.FP301.FunctionReturnEntries.fp_machineReturn args returnAddress emp)).

Definition fp301Table `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) : blockTable Sigma := {|
  block_table_code := decodeItemSelectedCode;
  block_table_entries := [
    (0x800d6960, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0000Entries.fp_machineAt0000 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6974, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0014Entries.fp_machineAt0014 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d697c, (ZesuSsz.Generated.DecodeItem.FP301.Pilot001cEntries.fp_machineAt001c args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d698c, (ZesuSsz.Generated.DecodeItem.FP301.Pilot002cEntries.fp_machineAt002c args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d69a4, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0044Entries.fp_machineAt0044 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d69b0, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0050Entries.fp_machineAt0050 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d69d8, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0078Entries.fp_machineAt0078 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d69e0, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0080Entries.fp_machineAt0080 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d69e8, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0088Entries.fp_machineAt0088 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a00, (ZesuSsz.Generated.DecodeItem.FP301.Pilot00a0Entries.fp_machineAt00a0 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a08, (ZesuSsz.Generated.DecodeItem.FP301.Pilot00a8Entries.fp_machineAt00a8 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a14, (ZesuSsz.Generated.DecodeItem.FP301.Pilot00b4Entries.fp_machineAt00b4 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a24, (ZesuSsz.Generated.DecodeItem.FP301.Pilot00c4Entries.fp_machineAt00c4 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a38, (ZesuSsz.Generated.DecodeItem.FP301.Pilot00d8Entries.fp_machineAt00d8 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a40, (ZesuSsz.Generated.DecodeItem.FP301.Pilot00e0Entries.fp_machineAt00e0 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a64, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0104Entries.fp_machineAt0104 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a6c, (ZesuSsz.Generated.DecodeItem.FP301.Pilot010cEntries.fp_machineAt010c args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6a78, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0118Entries.fp_machineAt0118 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6aa8, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0148Entries.fp_machineAt0148 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6ab4, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0154Entries.fp_machineAt0154 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6ac4, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0164Entries.fp_machineAt0164 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6ad8, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0178Entries.fp_machineAt0178 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6ae0, (ZesuSsz.Generated.DecodeItem.FP301.Pilot0180Entries.fp_machineAt0180 args returnAddress (fp301Continuation args returnAddress))%I);
    (0x800d6b08, (ZesuSsz.Generated.DecodeItem.FP301.Pilot01a8Entries.fp_machineAt01a8 args returnAddress (fp301Continuation args returnAddress))%I)
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
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0000.DesignedBoundary_800d6960 Sigma _ _) as Fp301Block_800d6960;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0000.DesignedEntry_800d6960 in Fp301Block_800d6960;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0014.DesignedBoundary_800d6974 Sigma _ _) as Fp301Block_800d6974;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0014.DesignedEntry_800d6974 in Fp301Block_800d6974;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller001c.DesignedBoundary_800d697c Sigma _ _) as Fp301Block_800d697c;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller001c.DesignedEntry_800d697c in Fp301Block_800d697c;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller002c.DesignedBoundary_800d698c Sigma _ _) as Fp301Block_800d698c;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller002c.DesignedEntry_800d698c in Fp301Block_800d698c;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0044.DesignedBoundary_800d69a4 Sigma _ _) as Fp301Block_800d69a4;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0044.DesignedEntry_800d69a4 in Fp301Block_800d69a4;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0050.DesignedBoundary_800d69b0 Sigma _ _) as Fp301Block_800d69b0;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0050.DesignedEntry_800d69b0 in Fp301Block_800d69b0;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0078.DesignedBoundary_800d69d8 Sigma _ _) as Fp301Block_800d69d8;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0078.DesignedEntry_800d69d8 in Fp301Block_800d69d8;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0080.DesignedBoundary_800d69e0 Sigma _ _) as Fp301Block_800d69e0;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0080.DesignedEntry_800d69e0 in Fp301Block_800d69e0;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0088.DesignedBoundary_800d69e8 Sigma _ _) as Fp301Block_800d69e8;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0088.DesignedEntry_800d69e8 in Fp301Block_800d69e8;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller00a0.DesignedBoundary_800d6a00 Sigma _ _) as Fp301Block_800d6a00;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller00a0.DesignedEntry_800d6a00 in Fp301Block_800d6a00;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller00a8.DesignedBoundary_800d6a08 Sigma _ _) as Fp301Block_800d6a08;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller00a8.DesignedEntry_800d6a08 in Fp301Block_800d6a08;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller00b4.DesignedBoundary_800d6a14 Sigma _ _) as Fp301Block_800d6a14;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller00b4.DesignedEntry_800d6a14 in Fp301Block_800d6a14;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller00c4.DesignedBoundary_800d6a24 Sigma _ _) as Fp301Block_800d6a24;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller00c4.DesignedEntry_800d6a24 in Fp301Block_800d6a24;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller00d8.DesignedBoundary_800d6a38 Sigma _ _) as Fp301Block_800d6a38;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller00d8.DesignedEntry_800d6a38 in Fp301Block_800d6a38;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller00e0.DesignedBoundary_800d6a40 Sigma _ _) as Fp301Block_800d6a40;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller00e0.DesignedEntry_800d6a40 in Fp301Block_800d6a40;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0104.DesignedBoundary_800d6a64 Sigma _ _) as Fp301Block_800d6a64;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0104.DesignedEntry_800d6a64 in Fp301Block_800d6a64;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller010c.DesignedBoundary_800d6a6c Sigma _ _) as Fp301Block_800d6a6c;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller010c.DesignedEntry_800d6a6c in Fp301Block_800d6a6c;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0118.DesignedBoundary_800d6a78 Sigma _ _) as Fp301Block_800d6a78;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0118.DesignedEntry_800d6a78 in Fp301Block_800d6a78;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0148.DesignedBoundary_800d6aa8 Sigma _ _) as Fp301Block_800d6aa8;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0148.DesignedEntry_800d6aa8 in Fp301Block_800d6aa8;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0154.DesignedBoundary_800d6ab4 Sigma _ _) as Fp301Block_800d6ab4;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0154.DesignedEntry_800d6ab4 in Fp301Block_800d6ab4;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0164.DesignedBoundary_800d6ac4 Sigma _ _) as Fp301Block_800d6ac4;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0164.DesignedEntry_800d6ac4 in Fp301Block_800d6ac4;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0178.DesignedBoundary_800d6ad8 Sigma _ _) as Fp301Block_800d6ad8;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0178.DesignedEntry_800d6ad8 in Fp301Block_800d6ad8;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller0180.DesignedBoundary_800d6ae0 Sigma _ _) as Fp301Block_800d6ae0;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller0180.DesignedEntry_800d6ae0 in Fp301Block_800d6ae0;
  pose proof (@ZesuSsz.Proofs.DecodeItem.FP301.Caller01a8.DesignedBoundary_800d6b08 Sigma _ _) as Fp301Block_800d6b08;
  unfold ZesuSsz.Proofs.DecodeItem.FP301.Caller01a8.DesignedEntry_800d6b08 in Fp301Block_800d6b08.

(* ---- Composition over the block table. ---- *)
Lemma fp301_decodeItem_body `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) :
  ⊢ □ decodeItemSelectedCode -∗
    instr_body 0x800d6960 (ZesuSsz.Generated.DecodeItem.FP301.Pilot0000Entries.fp_machineAt0000 args returnAddress
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
  ZesuSsz.Generated.DecodeItem.FP301.Pilot0000Entries.fp_machineAt0000_ForwardA0N0 args returnAddress ∗
  ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args⌝.
Proof.
  iIntros "(%a3 & %a4 & %a5 & %a6 & Hsys & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & H1 & H8 & Hin & Hout & Hstack & %Hdomain & _)".
  iSplit; [|done].
  iExists a3, a4, a5, a6, (BV 64 0), (BV 64 0), (BV 64 0).
  iFrame. iSplit; [done|].
  iSplit; [iPureIntro; exact (decodeItemDomainAtReturnAlignment returnAddress args Hdomain)|].
  iSplit; [done|]. iPureIntro. split; reflexivity.
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
  rewrite /ZesuSsz.Generated.DecodeItem.FP301.Pilot0000Entries.fp_machineAt0000.
  iFrame "Hforward".
  iApply (instr_pre_wand with "Hexit"); [done|done|].
  iIntros "Hreturn". by iApply (fp301_end_bridge with "Hreturn").
Qed.

(* The register exit weakens to the reviewed exit. *)
Lemma fp301_register_exit_weakens `{!islaG Sigma} `{!threadG} args after :
  decodeItemExitResourcesRegisters args after ⊢ decodeItemExitResources args after.
Proof.
  rewrite /decodeItemExitResourcesRegisters.
  iIntros "[Hbase _]". iExact "Hbase".
Qed.
