Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List.
Require Import isla.opsem.
Require Import isla.spec.
Require Import ZesuSsz.Contracts.OutputEvents.

Import ListNotations.

Definition writeOutputEvents (data size : bv 64) (payload : list (bv 8))
    (tail : spec) : spec :=
  scons (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data)
    (scons_snap (SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size)
      (fun snapshot =>
        read_mem_list snapshot.(snap_mem) (bv_unsigned data)
          (Z.to_N (bv_unsigned size)) = Some payload)
      tail).

Definition traceTrapRegister
    (labels : list seq_label) (pc : addr) (register : sail_name)
    (value : valu) : Prop :=
  exists snapshot,
    In (SInstrTrap pc snapshot) labels /\
    snapshot.(snap_regs) !! register = Some value.

Definition traceTrapMemory
    (labels : list seq_label) (pc : addr) (address : Z)
    (bytes : list byte) : Prop :=
  exists snapshot,
    In (SInstrTrap pc snapshot) labels /\
    read_mem_list snapshot.(snap_mem) address
      (N.of_nat (length bytes)) = Some bytes.

Definition traceWritePayload
    (labels : list seq_label) (address : addr) (value : bvn)
    (dataAddress : Z) (payload : list byte) : Prop :=
  exists snapshot,
    In (SWriteMem address value snapshot) labels /\
    read_mem_list snapshot.(snap_mem) dataAddress
      (N.of_nat (length payload)) = Some payload.

Lemma trap_snapshot_regs labels pc snapshot register value :
  In (SInstrTrap pc snapshot) labels ->
  snapshot.(snap_regs) !! register = Some value ->
  traceTrapRegister labels pc register value.
Proof. intros Hin Hlookup. exists snapshot. auto. Qed.

Lemma trap_snapshot_memory labels pc snapshot address bytes :
  In (SInstrTrap pc snapshot) labels ->
  read_mem_list snapshot.(snap_mem) address
    (N.of_nat (length bytes)) = Some bytes ->
  traceTrapMemory labels pc address bytes.
Proof. intros Hin Hread. exists snapshot. auto. Qed.

Lemma write_snapshot_payload labels address value snapshot dataAddress payload :
  In (SWriteMem address value snapshot) labels ->
  read_mem_list snapshot.(snap_mem) dataAddress
    (N.of_nat (length payload)) = Some payload ->
  traceWritePayload labels address value dataAddress payload.
Proof. intros Hin Hread. exists snapshot. auto. Qed.

Lemma write_output_events_payload data size payload tail firstSnapshot
    writeSnapshot labels :
  writeOutputEvents data size payload tail
    (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
     SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot :: labels) ->
  read_mem_list writeSnapshot.(snap_mem) (bv_unsigned data)
    (Z.to_N (bv_unsigned size)) = Some payload.
Proof.
  unfold writeOutputEvents, scons, scons_snap. naive_solver.
Qed.

Print Assumptions trap_snapshot_regs.
Print Assumptions trap_snapshot_memory.
Print Assumptions write_snapshot_payload.
Print Assumptions write_output_events_payload.
