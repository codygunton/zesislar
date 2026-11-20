Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation2.All.
From iris.proofmode Require Import environments.
Local Open Scope Z_scope.

(* The first conjunct of the existential is an equation over the witness
   that only the array resource behind it fixes: Lithium alone stops on it;
   the step moves it behind the resource, once, and the block closes. *)
Lemma defer_witness_pure_fires `{!islaG Sigma} `{!threadG}
    (a : Z) (bytes : list (bv 8)) (word : bv 16) :
  word = bv_concat 16 (nth 1 bytes 0%bv) (nth 0 bytes 0%bv) ->
  a ↦ₘ∗ bytes -∗
  (∃ x : list (bv 8) *ₗ (), ⌜word = bv_concat 16 (nth 1 x.1ₗ 0%bv) (nth 0 x.1ₗ 0%bv)⌝ ∗
     a ↦ₘ∗ x.1ₗ ∗ True).
Proof.
  intros Hword. iStartProof. iIntros "Hbytes".
  Fail liStep.
  ZesuSsz.Automation2.Hooks.zesu_defer_witness_pure.
  lazymatch goal with
  | |- envs_entails _ (∃ x, _ ↦ₘ∗ _ ∗ ⌜_⌝ ∗ True)%I => idtac
  end.
  Fail ZesuSsz.Automation2.Hooks.zesu_defer_witness_pure.
  repeat liAStep.
Qed.

(* A pure first conjunct that does not mention the binder is Lithium's
   ordinary side condition: refused. *)
Lemma defer_witness_pure_refuses_closed_fact `{!islaG Sigma} `{!threadG}
    (a : Z) (bytes : list (bv 8)) (word : bv 16) :
  word = bv_concat 16 (nth 1 bytes 0%bv) (nth 0 bytes 0%bv) ->
  a ↦ₘ∗ bytes -∗
  (∃ x : list (bv 8) *ₗ (), ⌜word = bv_concat 16 (nth 1 bytes 0%bv) (nth 0 bytes 0%bv)⌝ ∗
     a ↦ₘ∗ x.1ₗ ∗ True).
Proof.
  intros Hword. iStartProof. iIntros "Hbytes".
  Fail ZesuSsz.Automation2.Hooks.zesu_defer_witness_pure.
  repeat liAStep.
Qed.

(* A dependent pure fact followed by pure conjuncts only: no resource can fix
   the witness, and two such facts would be swapped back and forth: refused. *)
Lemma defer_witness_pure_refuses_pure_rest `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (word : bv 16) :
  word = bv_concat 16 (nth 1 bytes 0%bv) (nth 0 bytes 0%bv) ->
  ⊢@{iProp Sigma} (∃ x : list (bv 8) *ₗ (), ⌜word = bv_concat 16 (nth 1 x.1ₗ 0%bv) (nth 0 x.1ₗ 0%bv)⌝ ∗
       ⌜length x.1ₗ = length bytes⌝ ∗ True).
Proof.
  intros Hword. iStartProof.
  Fail ZesuSsz.Automation2.Hooks.zesu_defer_witness_pure.
  iExists (bytes, tt)ₗ. simpl. iSplit; [done|]. iSplit; done.
Qed.
