Require Import ZesuSsz.Automation2.All.
From Coq Require Import ZArith.ZArith NArith.NArith Lia.
Require Import ZesuSsz.Automation2.CodecArrayRead.
Require Import isla.riscv64.riscv64.
Import iris.proofmode.ltac_tactics.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.
Module M.
#[local] Remove Hints ZesuSsz.Automation2.All.zesu_codec_array_read_enabled : typeclass_instances.
Lemma closed_offset (base:Z) : True.
Proof.
 ZesuSsz.Automation2.MemoryAddress.zesu_integer_pointer_root constr:(bv_add (Z_to_bv 64%N base) (BV 64%N 8%Z)) ltac:(fun _ => idtac).
 exact I.
Qed.
Lemma symbolic_offset (base offset:Z) : True.
Proof.
 Fail ZesuSsz.Automation2.MemoryAddress.zesu_integer_pointer_root constr:(bv_add (Z_to_bv 64%N base) (Z_to_bv 64%N offset)) ltac:(fun _ => idtac).
 exact I.
Qed.
Lemma irrelevant : True.
Proof.
 Fail ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_read_lookup_goal.
 Fail ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation2.CodecArrayRead.ZesuStepCodecArrayRead).
 Fail ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_find.
 Fail ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_read_consumer.
 exact I.
Qed.
Lemma valid_read_shape `{!islaG Sigma} (Delta:environments.envs (iProp Sigma)) (address:Z) :
 environments.envs_entails Delta (find_in_context (FindMemMapsTo address) (fun _ => (∀ _ : bv 64%N, True)%I)) ->
 environments.envs_entails Delta (find_in_context (FindMemMapsTo address) (fun _ => (∀ _ : bv 64%N, True)%I)).
Proof.
 intro Hproof.
 ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_read_lookup_goal.
 Fail ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation2.CodecArrayRead.ZesuStepCodecArrayRead).
 Fail ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_find.
 exact Hproof.
Qed.

#[local] Instance codec_enabled : ZesuSsz.Automation2.CodecArrayRead.ZesuStepCodecArrayRead := {}.
Lemma consumer_success `{!islaG Sigma} (word source : bv 64%N) :
 (⊢ ∀ value : bv 64%N,
  ⌜value = Z_to_bv 64%N (little_endian_to_bv 8%N
    (take 8%nat (drop (Z.to_nat 0) (bv_to_little_endian 8%nat 8%N (bv_unsigned word)))))⌝ -∗
  ⌜source = value⌝ -∗ True -∗ (True : iProp Sigma))%I.
Proof.
 iStartProof.
 ZesuSsz.Automation2.CodecArrayRead.zesu_codec_array_read_consumer.
 done.
Qed.

End M.
Print Assumptions M.closed_offset.
Print Assumptions M.symbolic_offset.
Print Assumptions M.irrelevant.
Print Assumptions M.valid_read_shape.

Print Assumptions M.consumer_success.

Definition expected_closed_offset : forall base:Z, True := M.closed_offset.
Definition expected_symbolic_offset : forall base offset:Z, True := M.symbolic_offset.
Definition expected_irrelevant : True := M.irrelevant.
