From Coq Require Import ZArith.ZArith Lists.List.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation2.UninitRequest.
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

(* A callee's arguments, built from the requested list. The record and its
   domain measure lists of `bv 8`; the requested list's type is an alias. *)
Definition request_octet : Type := bv 8.
Record request_args := {
  request_args_input : list (bv 8);
  request_args_output : list (bv 8)
}.
Definition request_args_of (input output : list request_octet) : request_args :=
  {| request_args_input := input; request_args_output := output |}.
Definition request_args_domain (args : request_args) : Prop :=
  (length (request_args_input args) <= 64)%nat /\
  length (request_args_output args) = 40%nat.

Section length_choice.
  Context `{!islaG Sigma}.

  (* The length the step chooses for a request and continuation. *)
  Ltac chosen requested G :=
    let h := constr:(_ : @LiTactic Sigma _ (zesu_uninit_request_length requested G)) in
    let h := eval cbv beta zeta in h in
    lazymatch h with zesu_uninit_request_length_hint _ _ ?choice => choice end.

  (* No fact of the continuation states the length: the step chooses none. *)
  Goal True.
  Proof.
    let c := chosen (fun x : list (bv 8) => x)
      (fun x : list (bv 8) => ⌜x = x⌝ ∗ True : iProp Sigma)%I in
    constr_eq c (@None nat).
    exact I.
  Qed.

  (* A fact about another list's length does not choose it either. *)
  Goal forall other : list (bv 8), True.
  Proof.
    intros other.
    let c := chosen (fun x : list (bv 8) => x)
      (fun _ : list (bv 8) => ⌜length other = 8%nat⌝ ∗ True : iProp Sigma)%I in
    constr_eq c (@None nat).
    exact I.
  Qed.

  (* The length the fact states is the one chosen. *)
  Goal True.
  Proof.
    let c := chosen (fun x : list (bv 8) => x)
      (fun x : list (bv 8) => ⌜length x = 24%nat⌝ ∗ True : iProp Sigma)%I in
    constr_eq c (Some 24%nat).
    exact I.
  Qed.

  (* The length is read through the callee's domain and argument record, at
     another name of the list's element type. *)
  Goal forall input : list request_octet, True.
  Proof.
    intros input.
    let c := chosen (fun x : list request_octet *ₗ unit => x.1ₗ)
      (fun x : list request_octet *ₗ unit =>
        ⌜request_args_domain (request_args_of input x.1ₗ)⌝ ∗ True : iProp Sigma)%I in
    constr_eq c (Some 40%nat).
    exact I.
  Qed.
End length_choice.
