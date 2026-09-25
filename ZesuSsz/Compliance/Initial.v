Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
From iris.program_logic Require Import language.
From stdpp Require Import gmap.
Require Import isla.opsem.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.EndpointMemory.
Require Import ZesuSsz.Compliance.Program.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Compliance.Targets.
Require Import ZesuSsz.Generated.ApprovedProgram.
Require Import ZesuSsz.Export.Adequacy.
Require Import ZesuMachineMap.Machine.

Import ListNotations.

Definition endpointGeneralRegisters : list string :=
  ["x0"; "x1"; "x2"; "x3"; "x4"; "x5"; "x6"; "x7";
   "x8"; "x9"; "x10"; "x11"; "x12"; "x13"; "x14"; "x15";
   "x16"; "x17"; "x18"; "x19"; "x20"; "x21"; "x22"; "x23";
   "x24"; "x25"; "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Definition endpointInitialRegisters (startSp : Z)
    (mstatusBits satp : bv 64) (generalValue : string -> bv 64) : reg_map :=
  <["PC" := RVal_Bits (BV 64 (mapStartPc defaultMap))]> $
  <["x0" := RVal_Bits (BV 64 0)]> $
  <["x2" := RVal_Bits (Z_to_bv 64 startSp)]> $
  <["rv_enable_writable_misa" := RVal_Bool (mapEnableWritableMisa defaultMap)]> $
  <["rv_enable_rvc" := RVal_Bool (mapEnableRvc defaultMap)]> $
  <["rv_enable_fdext" := RVal_Bool (mapEnableFdext defaultMap)]> $
  <["rv_enable_dirty_update" := RVal_Bool (mapEnableDirtyUpdate defaultMap)]> $
  <["rv_mtval_has_illegal_inst_bits" :=
      RVal_Bool (mapMtvalHasIllegalInstBits defaultMap)]> $
  <["rv_insns_per_tick" := RVal_Bits (BV 64 (mapInsnsPerTick defaultMap))]> $
  List.fold_right
    (fun register regs => <[register := RVal_Bits (generalValue register)]> regs)
    (zesu_ram_sys_regs_map mstatusBits satp)
    endpointGeneralRegisters.

Definition zesuMachineInitialLocal (startSp : Z)
    (mstatusBits satp : bv 64) (generalValue : string -> bv 64) :
    seq_local_state := {|
  seq_trace := tnil;
  seq_regs := endpointInitialRegisters startSp mstatusBits satp generalValue;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition zesuMachineInitialGlobal (P : gmap addr isla_trace) (input : ByteString) : seq_global_state := {|
  seq_instrs := P;
  seq_mem := endpointInputMemory input
|}.

Definition zesuMachineInitial (P : gmap addr isla_trace) (startSp : Z) (mstatusBits satp : bv 64)
    (generalValue : string -> bv 64) (input : ByteString) : cfg isla_lang :=
  ([zesuMachineInitialLocal startSp mstatusBits satp generalValue],
    zesuMachineInitialGlobal P input).

Lemma endpoint_initial_pc startSp mstatusBits satp generalValue :
  (endpointInitialRegisters startSp mstatusBits satp generalValue) !! "PC" =
    Some (RVal_Bits (BV 64 (mapStartPc defaultMap))).
Proof. apply lookup_insert. Qed.

Lemma endpoint_initial_x0 startSp mstatusBits satp generalValue :
  (endpointInitialRegisters startSp mstatusBits satp generalValue) !! "x0" =
    Some (RVal_Bits (BV 64 0)).
Proof.
  unfold endpointInitialRegisters.
  rewrite lookup_insert_ne; last discriminate.
  apply lookup_insert.
Qed.

Lemma endpoint_initial_stack startSp mstatusBits satp generalValue :
  (endpointInitialRegisters startSp mstatusBits satp generalValue) !! "x2" =
    Some (RVal_Bits (Z_to_bv 64 startSp)).
Proof.
  unfold endpointInitialRegisters.
  rewrite lookup_insert_ne; last discriminate.
  rewrite lookup_insert_ne; last discriminate.
  apply lookup_insert.
Qed.

Definition zesuStartSp : Z := machineRamEnd defaultMap - 0x1000.

Definition zesuInitial (P : AdmissibleProgram) (input : ByteString) :
    cfg isla_lang :=
  zesuMachineInitial (programInstructions P) zesuStartSp (BV 64 (mapMstatusValue defaultMap))
    (BV 64 0) (fun _ => BV 64 0) input.

Lemma zesu_initial_main_instruction P input :
  (snd (zesuInitial P input)).(seq_instrs) !! BV 64 (mapMainPc defaultMap) =
    Some IslaTraces.main.a14cb0.a14cb0.
Proof.
  unfold zesuInitial, zesuMachineInitial, zesuMachineInitialGlobal. simpl.
  apply approved_program_no_shadow. exact approved_main_instruction.
Qed.

Lemma zesu_initial_input_byte P input offset byte :
  InputWithinBound input ->
  input !! offset = Some byte ->
  (snd (zesuInitial P input)).(seq_mem) !!
    Z_to_bv 64 (mapInputBufferAddress defaultMap + Z.of_nat offset) =
    Some (Z_to_bv 8 byte).
Proof. intros Hbound Hbyte. exact (endpoint_input_byte input offset byte Hbound Hbyte). Qed.

Lemma zesu_initial_nonvacuous P input :
  InputWithinBound input ->
  (snd (zesuInitial P input)).(seq_instrs) !! BV 64 (mapMainPc defaultMap) =
    Some IslaTraces.main.a14cb0.a14cb0 /\
  forall offset byte, input !! offset = Some byte ->
    (snd (zesuInitial P input)).(seq_mem) !!
      Z_to_bv 64 (mapInputBufferAddress defaultMap + Z.of_nat offset) =
      Some (Z_to_bv 8 byte).
Proof.
  intros Hbound. split.
  - apply zesu_initial_main_instruction.
  - intros offset byte Hbyte. apply zesu_initial_input_byte; assumption.
Qed.

Print Assumptions zesu_initial_nonvacuous.
