(* Focused controls for the switched composition and its refusal boundaries. *)
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation.ArrayContinuation.
Import ListNotations.
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

Lemma array_continuation_missing_length (address : Z)
    (bytes storage : list (bv 8)) (count : nat) :
  address ↦ₘ∗ bytes -∗
    address ↦ₘ∗ bytes ∗ ⌜length storage = count⌝.
Proof.
  assert (enabled : ZesuStepArrayContinuation) by constructor.
  iIntros "Hbytes".
  Fail zesu_array_continuation ltac:(reflexivity).
Abort.

Lemma array_continuation_missing_payload (address : Z)
    (source target : list (bv 8)) :
  address ↦ₘ∗ source -∗ address ↦ₘ∗ target.
Proof.
  assert (enabled : ZesuStepArrayContinuation) by constructor.
  iIntros "Hbytes".
  Fail zesu_array_continuation ltac:(assumption).
Abort.

Lemma array_continuation_wrong_shape : True.
Proof.
  assert (enabled : ZesuStepArrayContinuation) by constructor.
  Fail zesu_array_continuation ltac:(fail "callback must not run").
  exact I.
Qed.

Lemma array_continuation_keeps_frame (address : Z)
    (source target : list (bv 8)) (K : iProp Sigma)
    (Hpayload : source = target) :
  address ↦ₘ∗ source -∗ address ↦ₘ∗ target ∗ K.
Proof.
  assert (enabled : ZesuStepArrayContinuation) by constructor.
  iIntros "Hbytes".
  Fail zesu_array_continuation ltac:(assumption).
Abort.

Lemma array_continuation_wrong_address (source_address target_address : Z)
    (bytes : list (bv 8)) :
  source_address ↦ₘ∗ bytes -∗ target_address ↦ₘ∗ bytes.
Proof.
  assert (enabled : ZesuStepArrayContinuation) by constructor.
  iIntros "Hbytes".
  Fail zesu_array_continuation ltac:(reflexivity).
Abort.

Lemma array_continuation_wrong_fraction (address : Z)
    (bytes : list (bv 8)) (source_fraction target_fraction : dfrac) :
  mem_mapsto_array address source_fraction bytes -∗
    mem_mapsto_array address target_fraction bytes.
Proof.
  assert (enabled : ZesuStepArrayContinuation) by constructor.
  iIntros "Hbytes".
  Fail zesu_array_continuation ltac:(reflexivity).
Abort.
End controls.
