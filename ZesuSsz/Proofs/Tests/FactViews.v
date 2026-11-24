Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import stdpp.bitvector.definitions.
From iris.proofmode Require Import environments.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require ZesuSsz.Automation2.ResidualExport.
From Ltac2 Require Import Ltac2.
From Coq Require Import Lia.
Require Import ZesuSsz.Automation2.All.
Set Default Proof Mode "Classic".
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

  (* A token whose size is a long expression, as an allocation size computed
     by a growth formula is. Its fact states the size three times and lies
     above the solvers' node limit, so neither a solver's context selection
     nor a residual statement sees it; each piece states the size at most
     twice and lies below the limit. *)
  Local Notation big4 y := (y + y + y + y) (only parsing).
  Local Notation bigSize y := (big4 (big4 (big4 (big4 y)))) (only parsing).

  Definition alignedToken (pointer bytes : Z) : iProp Sigma :=
    ((pointer + bytes) ↦ₘ? 8 ∗
     ⌜bytes <> 0 -> 4096 <= pointer /\ pointer + bytes <= 8192 /\ (bytes | pointer)⌝)%I.
  Lemma alignedToken_unfold (pointer bytes : Z) :
    alignedToken pointer bytes ⊣⊢
    ((pointer + bytes) ↦ₘ? 8 ∗
     ⌜bytes <> 0 -> 4096 <= pointer /\ pointer + bytes <= 8192 /\ (bytes | pointer)⌝)%I.
  Proof. reflexivity. Qed.
  Global Opaque alignedToken.

  #[local] Instance alignedTokenFactView (pointer bytes : Z) :
    ZesuFactView (alignedToken pointer bytes)
      (bytes <> 0 -> 4096 <= pointer /\ pointer + bytes <= 8192 /\ (bytes | pointer)).
  Proof.
    rewrite /ZesuFactView alignedToken_unfold.
    iIntros "[Hslack %Hfacts]". iFrame "Hslack". iSplit; iPureIntro; exact Hfacts.
  Qed.

  (* The loss: the entry scan poses the fact, which lies above the node
     limit, so the exported statement does not carry it. With its pieces
     posed (as the exporter does, on a context it restores), the statement
     carries all three. *)
  Lemma fact_view_large_fact_export (pointer y : Z) :
    alignedToken pointer (bigSize y) -∗ ⌜bigSize y <> 0 -> pointer + bigSize y < 8193⌝.
  Proof.
    iStartProof. iIntros "Htoken". FactViews.zesu_pose_fact_views.
    iPureIntro. intros Hnz.
    ltac2:(
      let (facts, _, _) := ResidualExport.zesu_export_reach 2048 in
      let (statement, _) := ResidualExport.zesu_export_statement facts in
      if Constr.equal statement constr:(forall (pointer y : Z) (Hnz : bigSize y <> 0),
          pointer + bigSize y < 8193)
      then () else Control.throw (Tactic_failure None)).
    ltac2:(ResidualExport.zesu_export_goal "final").
    lazymatch goal with _ : bigSize y <> 0 -> 4096 <= pointer |- _ => fail | _ => idtac end.
    ltac2:(
      let _ := ZesuSsz.Automation2.ContextCollection.zesu_large_fact_pieces () in
      let (facts, _, _) := ResidualExport.zesu_export_reach 2048 in
      let (statement, _) := ResidualExport.zesu_export_statement facts in
      if Constr.equal statement constr:(forall (pointer y : Z) (Hnz : bigSize y <> 0)
          (H1 : bigSize y <> 0 -> 4096 <= pointer)
          (H2 : bigSize y <> 0 -> pointer + bigSize y <= 8192)
          (H3 : bigSize y <> 0 -> (bigSize y | pointer)), pointer + bigSize y < 8193)
      then () else Control.throw (Tactic_failure None)).
    lia.
  Qed.

  (* A residual lemma stated over a piece, registered in the relocatable
     (exact) form, closes the goal at the tier's last try. *)
  Lemma residual_piece_lemma (pointer y : Z)
      (Hnz : bigSize y <> 0) (Hpiece : bigSize y <> 0 -> pointer + bigSize y <= 8192) :
    pointer + bigSize y < 8193.
  Proof. lia. Qed.
  #[local] Hint Extern 0 => ZesuSsz.Automation2.ResidualLemmas.zesu_residual_exact
    constr:(residual_piece_lemma) : zesu_residual_exact.

  Lemma fact_view_large_fact_residual (pointer y : Z) :
    alignedToken pointer (bigSize y) -∗ ⌜bigSize y <> 0 -> pointer + bigSize y < 8193⌝.
  Proof.
    iStartProof. iIntros "Htoken". FactViews.zesu_pose_fact_views.
    iPureIntro. intros Hnz.
    Fail solve [typeclasses eauto 1 with zesu_residual_exact].
    ResidualLemmas.zesu_residual_lemma.
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
