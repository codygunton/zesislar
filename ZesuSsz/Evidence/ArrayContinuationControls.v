(* Focused controls for the switched composition and its refusal boundaries. *)
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation.ArrayContinuation.
Import ListNotations.
Require Import ZesuSsz.Automation.All.
Local Open Scope Z_scope.

Section controls.
Context `{!islaG Sigma} `{!threadG}.

Lemma array_continuation_disabled (address : Z) (bytes : list (bv 8)) :
  address ↦ₘ∗ bytes -∗ address ↦ₘ∗ bytes.
Proof.
  iIntros "Hbytes".
  Fail zesu_array_continuation ltac:(reflexivity).
  iExact "Hbytes".
Qed.

Lemma array_continuation_payload (address : Z)
    (source target storage : list (bv 8)) (count : nat) (K : iProp Sigma)
    (Hpayload : source = target) (Hlength : length storage = count) :
  address ↦ₘ∗ source ∗ K -∗
  address ↦ₘ∗ target ∗
    ⌜length (take (Z.to_nat (address - address)) storage ++
       drop (Z.to_nat (address - address)) storage) = count⌝ ∗ K.
Proof.
  assert (enabled : ZesuStepArrayContinuation) by constructor.
  iIntros "[Hbytes HK]".
  zesu_array_continuation ltac:(assumption).
Qed.



Lemma array_continuation_wrong_shape : True.
Proof.
  assert (enabled : ZesuStepArrayContinuation) by constructor.
  Fail zesu_array_continuation ltac:(fail "callback must not run").
  exact I.
Qed.



End controls.
