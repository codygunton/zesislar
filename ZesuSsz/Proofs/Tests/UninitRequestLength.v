From Coq Require Import ZArith.ZArith Lists.List.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A callee asks for an output buffer inside an uninitialized frame region, and
   only a later pure fact of its precondition fixes the buffer's length. The
   witness is chosen after the region's bytes; the fact gives the length. *)
Lemma uninit_request_length_from_fact `{!islaG Sigma} (base : Z) (P : list (bv 8) -> Prop) :
  0 <= base -> base + 320 < 2 ^ 64 ->
  (forall v, length v = 40%nat -> P v) ->
  base ↦ₘ? 320 -∗
  ∃ before : list (bv 8), (base + 8) ↦ₘ∗ before ∗ ⌜length before = 40%nat /\ P before⌝ ∗ True.
Proof.
  intros Hbase Hbound HP. iStartProof. liARun.
  Unshelve. all: try (prepare_sidecond; first [assumption | lia | (apply HP; assumption)]).
Qed.

(* The length sits behind a definition of the fact, as in a callee's domain. *)
Definition request_domain (before : list (bv 8)) : Prop := 0 <= 1 /\ length before = 16%nat.

Lemma uninit_request_length_unfolded `{!islaG Sigma} (base : Z) :
  0 <= base -> base + 64 < 2 ^ 64 ->
  base ↦ₘ? 64 -∗
  ∃ before : list (bv 8), (base + 16) ↦ₘ∗ before ∗ ⌜request_domain before⌝ ∗ True.
Proof.
  intros Hbase Hbound. iStartProof. liARun.
  Unshelve. all: try (prepare_sidecond; first [assumption | lia | (split; [lia | assumption])]).
Qed.

Section length_choice.
  Context `{!islaG Sigma}.

  (* No fact of the continuation states the length: the step does not choose one. *)
  Goal LiTactic (mem_uninit_request_length (fun x : list (bv 8) => x)
    (fun x => ⌜x = x⌝ ∗ True)%I).
  Proof.
    Fail mem_uninit_request_length_solve.
    exact (mem_uninit_request_length_hint _ _ 0).
  Qed.

  (* A fact about another list's length does not choose it either. *)
  Goal forall other : list (bv 8),
    LiTactic (mem_uninit_request_length (fun x : list (bv 8) => x)
      (fun _ => ⌜length other = 8%nat⌝ ∗ True)%I).
  Proof.
    intros other.
    Fail mem_uninit_request_length_solve.
    exact (mem_uninit_request_length_hint _ _ 0).
  Qed.

  (* The length the fact states is the one chosen. *)
  Goal LiTactic (mem_uninit_request_length (fun x : list (bv 8) => x)
    (fun x => ⌜length x = 24%nat⌝ ∗ True)%I).
  Proof. mem_uninit_request_length_solve. Qed.
End length_choice.
