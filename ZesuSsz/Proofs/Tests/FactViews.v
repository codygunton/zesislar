Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import stdpp.bitvector.definitions.
From iris.proofmode Require Import environments.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Section fact_views.
  Context `{!islaG Sigma} `{!threadG}.

  (* A sealed token whose pure part bounds its pointer, sealed as the
     allocator's block token is: an unfold lemma, an opaque boundary and a
     registered fact view. *)
  Definition viewToken (pointer bytes : Z) : iProp Sigma :=
    ((pointer + bytes) ↦ₘ? 8 ∗
     ⌜bytes <> 0 -> 4096 <= pointer /\ pointer + bytes <= 8192⌝)%I.
  Lemma viewToken_unfold (pointer bytes : Z) :
    viewToken pointer bytes ⊣⊢
    ((pointer + bytes) ↦ₘ? 8 ∗
     ⌜bytes <> 0 -> 4096 <= pointer /\ pointer + bytes <= 8192⌝)%I.
  Proof. reflexivity. Qed.
  Global Opaque viewToken.

  #[local] Instance viewTokenFactView (pointer bytes : Z) :
    ZesuFactView (viewToken pointer bytes)
      (bytes <> 0 -> 4096 <= pointer /\ pointer + bytes <= 8192).
  Proof.
    rewrite /ZesuFactView viewToken_unfold.
    iIntros "[Hslack %Hfacts]". iFrame "Hslack". iSplit; iPureIntro; exact Hfacts.
  Qed.

  (* A side condition read from the token: Lithium introduces the token and
     its fact; the side condition's solver reads the fact. *)
  Lemma fact_view_side_condition (pointer : Z) :
    ⊢ viewToken pointer 64 -∗ ⌜pointer + 64 <= 8192⌝ ∗ viewToken pointer 64.
  Proof.
    iStartProof. ZesuSsz.Automation2.Finish.zesu_run.
  Qed.

  (* The same side condition with the token already held (a block entry):
     the entry scan poses the fact once. *)
  Lemma fact_view_entry_scan (pointer : Z) :
    viewToken pointer 64 -∗ ⌜4096 <= pointer⌝ ∗ viewToken pointer 64.
  Proof.
    iStartProof. iIntros "Htoken".
    FactViews.zesu_pose_fact_views. FactViews.zesu_pose_fact_views.
    lazymatch goal with
    | H1 : 64 <> 0 -> _, H2 : 64 <> 0 -> _ |- _ => fail
    | _ : 64 <> 0 -> 4096 <= pointer /\ pointer + 64 <= 8192 |- _ => idtac
    end.
    ZesuSsz.Automation2.Finish.zesu_run.
  Qed.

  (* A resource without a view is introduced as before. *)
  Lemma fact_view_no_instance (pointer : Z) :
    pointer ↦ₘ? 8 -∗ pointer ↦ₘ? 8.
  Proof.
    iStartProof. iIntros "Hcell". FactViews.zesu_pose_fact_views.
    lazymatch goal with
    | _ : _ -> _ |- _ => fail
    | _ => idtac
    end.
    ZesuSsz.Automation2.Finish.zesu_run.
  Qed.

  (* The allocator's block token: its range enters at Lithium's
     introduction, ready for a caller that writes the block. *)
  Lemma alt_fl_block_fact_view (pointer bytes log2Align : Z) :
    ⊢ altFlBlock pointer bytes log2Align -∗
      ⌜bytes <> 0 ->
       mapRamBase defaultMap <= pointer /\
       pointer + bytes <= machineRamEnd defaultMap /\
       (altFlBlockAlignment bytes log2Align | pointer)⌝ ∗
      altFlBlock pointer bytes log2Align.
  Proof.
    iStartProof. ZesuSsz.Automation2.Finish.zesu_run.
  Qed.
End fact_views.

(* A vacuous branch: a value a callee premise fixed at 0 and a not-taken
   branch on it. Either order of either fact, any width. *)
Goal forall x : bv 64, bv_unsigned x = 0 -> x <> 0%bv -> False.
Proof.
  intros x Hzero Hbranch. ZesuSsz.Automation2.Finish.zesu_finish_shape_closers.
Qed.

Goal forall (x : bv 32) (y : Z), 0 = bv_unsigned x -> BV 32 0 <> x -> y = 5.
Proof.
  intros x y Hzero Hbranch. ZesuSsz.Automation2.Finish.zesu_finish_shape_closers.
Qed.

(* A nonzero constant: no contradiction. *)
Goal forall x : bv 64, bv_unsigned x = 0 -> x <> BV 64 1 -> True.
Proof.
  intros x Hzero Hbranch.
  Fail ZesuSsz.Automation2.Finish.zesu_bv_zero_contradiction.
  exact I.
Qed.
