(* These controls check the canonical release rule set. *)
Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
From stdpp Require Import bitvector.definitions list.
Import ListNotations.
Local Open Scope Z_scope.

Lemma v34_all_selects_candidates : True.
Proof.
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.SignedMaskBranch.ZesuStepSignedMaskBranch).
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.ArrayContinuation.ZesuStepArrayContinuation).
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.WordIdentity.ZesuStepWordIdentity).
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.CodecArrayRead.ZesuStepCodecArrayRead).
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.Hooks.ZesuStepRegcolVMCompute).
  exact I.
Qed.

(* The native caller imports this same release rule set. *)
Require Import ZesuSsz.Automation.All.

Lemma v34_selected_switches_reach_search : True.
Proof.
  let switches := zesu_search_switches in
  ZesuSsz.Automation.SwitchDispatch.zesu_with_switches switches ltac:(fun _ =>
    ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.SignedMaskBranch.ZesuStepSignedMaskBranch);
    ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.ArrayContinuation.ZesuStepArrayContinuation);
    ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.WordIdentity.ZesuStepWordIdentity);
    ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.CodecArrayRead.ZesuStepCodecArrayRead);
    ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.CodecArrayRange.ZesuStepCodecArrayRange);
    ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.ByteArrayLengths.ZesuStepArrayRegionBounds);
    ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.Hooks.ZesuStepArrayBounds);
    ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.Hooks.ZesuStepRegcolVMCompute);
    exact I).
Qed.

Lemma v34_word_union_consumer (digits : list Z) :
  (0%bv : bv 64) =
    Z_to_bv 64 (fold_left Z.add (firstn (Z.to_nat 0) digits) 0).
Proof. zesu_union_required_pure. Qed.

Lemma v34_word_residual_consumer (base : Z) :
  bv_add (Z_to_bv 64 base) (Z_to_bv 64 (-5)) = Z_to_bv 64 (base - 5).
Proof. zesu_finish_residual_cascade. Qed.

Lemma v34_signed_union_consumer (payload view : bv 16)
    (link : bv_and payload (BV 16 255) = view)
    (branch : bv_signed (bv_zero_extend 32 view) >= bv_signed (BV 32 17)) :
  bv_signed (bv_zero_extend 32 (bv_and payload (BV 16 255))) >=
    bv_signed (BV 32 17).
Proof. zesu_union_required_pure. Qed.

Lemma v34_signed_residual_consumer (payload view : bv 16)
    (link : bv_and payload (BV 16 255) = view)
    (branch : ~ bv_signed (bv_zero_extend 32 view) >= bv_signed (BV 32 17)) :
  ~ bv_signed (bv_zero_extend 32 (bv_and payload (BV 16 255))) >=
    bv_signed (BV 32 17).
Proof. zesu_finish_residual_cascade. Qed.

Lemma v34_closed_vm_consumer : (BV 64 2 + BV 64 3)%bv = BV 64 5.
Proof. zesu_finish_constant. Qed.

Lemma v34_symbolic_vm_refusal (word : bv 64) : word = word.
Proof. Fail zesu_finish_constant. reflexivity. Qed.

Section spatial_consumers.
Context `{!islaG Sigma} `{!threadG}.

Lemma v34_array_search_consumer (address : Z)
    (source target storage : list (bv 8)) (count : nat) (K : iProp Sigma)
    (Hpayload : source = target) (Hlength : length storage = count) :
  address ↦ₘ∗ source ∗ K -∗
    address ↦ₘ∗ target ∗
      ⌜length (take (Z.to_nat (address - address)) storage ++
        drop (Z.to_nat (address - address)) storage) = count⌝ ∗ K.
Proof.
  iIntros "[Hbytes HK]".
  zesu_run_pass_steps.
Qed.

Lemma v34_codec_search_consumer (base : Z) (fraction : dfrac)
    (a b : bv 8) (word loaded : bv 16) (K : iProp Sigma) :
  K -∗
  ∀ value : bv 16,
    ⌜value = Z_to_bv 16 (little_endian_to_bv 8
      (take 2 (drop (Z.to_nat (base + 2 - base))
        (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word)))))⌝ -∗
    ⌜loaded = value⌝ -∗
    base ↦ₘ{fraction}∗ (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word)) -∗
    base ↦ₘ{fraction}∗ (a :: b :: bv_to_little_endian 2 8 (bv_unsigned word)) ∗ K.
Proof.
  iIntros "HK".
  zesu_run_pass_steps.
  iFrame.
Qed.
End spatial_consumers.

Lemma v34_codec_exposed_sidecondition : SHELVED_SIDECOND ((0 <= 4 - 2)%Z).
Proof. zesu_codec_array_read_sidecond. Qed.

Lemma v34_wrong_shape_keeps_goal : True.
Proof.
  Fail zesu_word_identity.
  Fail zesu_signed_mask_branch.
  Fail zesu_array_continuation ltac:(fail "callback must not run").
  Fail zesu_codec_array_read.
  exact I.
Qed.
