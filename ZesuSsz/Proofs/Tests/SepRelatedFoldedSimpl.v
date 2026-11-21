Require Import isla.riscv64.riscv64.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Open Scope Z_scope.

(* Lithium's `liSep` and `liFindInContext` (redefined in Automation2/Hooks.v)
   simplify the goal with the bitvector moduli folded, like `liSimpl`. The
   probe fact below decides on a computed modulus: plain simpl computes
   `bv_modulus 2` and reduces the fact to `true = true` (first lemma); the
   folded simpl leaves it as it is. *)

Section sep.
Context `{!islaG Sigma} `{!threadG}.

Lemma plain_simpl_computes_modulus (w : bv 64) :
  "x1" ↦ᵣ RVal_Bits w ⊢
  "x1" ↦ᵣ RVal_Bits (bv_add w (BV 64 0)) ∗
  ⌜match bv_modulus 2 with Zpos _ => true | _ => false end = true⌝.
Proof.
  iIntros "H".
  simpl.
  tryif (lazymatch goal with |- context[bv_modulus 2] => idtac end)
  then fail "plain simpl kept the modulus" else idtac.
  iSplitL.
  { by rewrite bv_add_0_r. }
  done.
Qed.

(* A register asked with another spelling of the held value: liSep finds it
   through `RelatedTo` (whole-goal simpl, then liFindInContext and its own
   simpl). Neither computes the probe fact; the lookup still works. *)
Lemma sep_related_folds_moduli (w : bv 64) :
  "x1" ↦ᵣ RVal_Bits w ⊢
  "x1" ↦ᵣ RVal_Bits (bv_add w (BV 64 0)) ∗
  ⌜match bv_modulus 2 with Zpos _ => true | _ => false end = true⌝.
Proof.
  iIntros "H".
  liSep.
  lazymatch goal with
  | |- environments.envs_entails _ (subsume _ _ ?T) =>
      lazymatch T with context[bv_modulus 2] => idtac end
  end.
  iIntros "H". iExists tt. iSplitL.
  { by rewrite bv_add_0_r. }
  iPureIntro. reflexivity.
Qed.

End sep.

Print Assumptions sep_related_folds_moduli.
