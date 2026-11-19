Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
From iris.proofmode Require Import environments tactics.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* Guard of MaskWitness.zesu_mask_witness_telescope: a linear comparison
   among the conjuncts that do not mention the witnesses must follow from the
   context by linear arithmetic before the telescope commits. *)
Section mask_independent_guard_tests.
  Context `{!islaG Sigma} `{!threadG}.

  (* Fires: the independent comparison follows from a context range fact. *)
  Lemma mask_independent_linear_fires (status : bv 64) (x : Z)
      (Hstatus : Z.land (bv_unsigned status) 8 = 0) (Hx : 200 <= x) :
    ⊢@{iProp Sigma} ∃ p : bv 64 *ₗ unit,
      ⌜bv_and p.1ₗ (BV 64 8) = BV 64 0⌝ ∗ ⌜192 <= x⌝.
  Proof.
    iStartProof.
    MaskWitness.zesu_mask_witness_telescope.
    iSplit; iPureIntro; [MaskWitness.zesu_mask_fact_close | lia].
  Qed.

  (* Skipped: the independent comparison is a path fact the context states
     only in another form (the shape of decodeItem 001c and 00a0, where a
     source route proves it); the telescope is left to that route. *)
  Lemma mask_independent_linear_skips (status : bv 64) (x : Z) (f : Z -> bool)
      (Hstatus : Z.land (bv_unsigned status) 8 = 0)
      (Hspec : forall y, f y = true -> 192 <= y) (Hf : f x = true) :
    ⊢@{iProp Sigma} ∃ p : bv 64 *ₗ unit,
      ⌜bv_and p.1ₗ (BV 64 8) = BV 64 0⌝ ∗ ⌜192 <= x⌝.
  Proof.
    iStartProof.
    Fail MaskWitness.zesu_mask_witness_telescope.
    iExists (li_pair status tt). cbv [li_fst li_snd].
    iSplit; iPureIntro; [MaskWitness.zesu_mask_fact_close | exact (Hspec x Hf)].
  Qed.
End mask_independent_guard_tests.
