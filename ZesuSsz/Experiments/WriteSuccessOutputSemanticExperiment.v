From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.

Import ListNotations.

Definition writeSuccessPublicBytes (bytes : list (bv 8)) : ByteString :=
  List.map bv_unsigned bytes.

(** The MMIO descriptor needs a memory snapshot to determine output bytes. *)
Definition writeOutputPayloadObservation
    (memoryAtWrite : bv 64 -> list (bv 8) -> Prop)
    (data size : bv 64) (bytes : ByteString) : Prop :=
  exists payload : list (bv 8),
    memoryAtWrite data payload /\
    bv_unsigned size = Z.of_nat (length payload) /\
    bytes = writeSuccessPublicBytes payload.

(** [scons] is prefix closed, so the event specification permits no events. *)
Lemma write_output_events_accept_empty (data size : bv 64) (tail : spec) :
  writeOutputEvents data size tail [].
Proof. unfold writeOutputEvents, scons. auto. Qed.

Lemma write_output_events_accept_descriptor_prefix
    (data size : bv 64) (tail : spec) :
  writeOutputEvents data size tail
    [SWriteMem (BV 64 0x2401a0c0) data;
     SWriteMem (BV 64 0x2401a0c8) size].
Proof. unfold writeOutputEvents, scons. naive_solver. Qed.

Lemma write_output_payload_observation
    (memoryAtWrite : bv 64 -> list (bv 8) -> Prop)
    (data : bv 64) (payload : list (bv 8))
    (Hlength : (length payload < 2 ^ 64)%nat)
    (Hmemory : memoryAtWrite data payload) :
  writeOutputPayloadObservation memoryAtWrite data
    (Z_to_bv 64 (Z.of_nat (length payload)))
    (writeSuccessPublicBytes payload).
Proof.
  exists payload. split; [exact Hmemory |].
  split; [|reflexivity].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  split; [lia |].
  change (Z.of_nat (length payload) < 2 ^ 64)%Z.
  apply Nat2Z.inj_lt in Hlength.
  rewrite Nat2Z.inj_pow in Hlength. exact Hlength.
Qed.
