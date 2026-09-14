Require Import ZesuSsz.Automation.All.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.ReadInput.ReadInput.

Definition mainInputOfSnapshot (snapshot : seq_snapshot) : option ByteString :=
  match read_mem_list snapshot.(snap_mem) 0x2401a0b8 8 with
  | Some sizeBytes =>
      (List.map bv_unsigned) <$>
        read_mem_list snapshot.(snap_mem) 0x2001a000
          (Z.to_N (little_endian_to_bv 8 sizeBytes))
  | None => None
  end.

Lemma main_snapshot_input_bytes snapshot input :
  mainInputOfSnapshot snapshot = Some input ->
  Forall (fun value => (0 <= value < 256)%Z) input.
Proof.
  unfold mainInputOfSnapshot.
  destruct (read_mem_list (snap_mem snapshot) 0x2401a0b8 8) as [sizeBytes|]; last discriminate.
  destruct (read_mem_list (snap_mem snapshot) 0x2001a000
    (Z.to_N (little_endian_to_bv 8 sizeBytes))) as [bytes|]; last discriminate.
  intros Hinput. inversion Hinput; subst input.
  apply Forall_map, Forall_forall. intros value Hin.
  apply bv_unsigned_in_range.
Qed.

Lemma main_input_memory_roundtrip (bytes : list (bv 8)) :
  readInputMemory (List.map bv_unsigned bytes) = bytes.
Proof.
  unfold readInputMemory. rewrite List.map_map.
  induction bytes as [|value bytes IH]; simpl; first reflexivity.
  rewrite Z_to_bv_bv_unsigned IH. reflexivity.
Qed.
Print Assumptions main_snapshot_input_bytes.
Print Assumptions main_input_memory_roundtrip.

Fixpoint mainInputOfTrace (labels : list seq_label) : option ByteString :=
  match labels with
  | [] => None
  | SInstrTrap _ snapshot :: rest =>
      match mainInputOfSnapshot snapshot with
      | Some input => Some input
      | None => mainInputOfTrace rest
      end
  | _ :: rest => mainInputOfTrace rest
  end.

Lemma main_trace_input_bytes labels input :
  mainInputOfTrace labels = Some input ->
  Forall (fun value => 0 <= value < 256)%Z input.
Proof.
  induction labels as [|label labels IH]; simpl; first discriminate.
  destruct label; try apply IH.
  destruct (mainInputOfSnapshot s) eqn:Hsnapshot; last apply IH.
  intros Hinput. inversion Hinput; subst.
  eapply main_snapshot_input_bytes. exact Hsnapshot.
Qed.
Print Assumptions main_trace_input_bytes.
