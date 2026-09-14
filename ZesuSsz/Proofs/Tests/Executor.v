Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Export.Executor.
Require Import isla.opsem.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.instrs.
Require Import IslaTraces.write_success_02.instrs.
Require Import IslaTraces.write_success_07.instrs.
Require Import IslaTraces.write_success_90.instrs.
Require Import IslaTraces.write_success_91.instrs.
Require Import IslaTraces.write_success_92.instrs.
Require Import IslaTraces.write_success_93.instrs.
Require Import IslaTraces.write_success_94.instrs.
Require Import IslaTraces.write_success_95.instrs.

Definition executor_test_regs (pc : Z) : reg_map :=
  <["PC" := RVal_Bits (Z_to_bv 64 pc)]>
  (<["x1" := RVal_Bits (Z_to_bv 64
    (if Z.eqb pc 0x15d28 then 0xfd24 else
     if Z.eqb pc 0x156a4 then 0x106a0 else
     if Z.eqb pc 0x156b0 then 0x156ac else
     if Z.eqb pc 0x156bc then 0x156b8 else
     if Z.eqb pc 0x156cc then 0x106c8 else
     if Z.eqb pc 0x156d8 then 0x156d4 else 0x156e8))]>
  (<["x5" := RVal_Bits (BV 64 0x2401a0b8)]>
  (<["x9" := RVal_Bits (BV 64 1)]>
  (<["x15" := RVal_Bits (BV 64 0)]>
  (list_to_map
    ([
      ("rv_enable_pmp", RVal_Bool false);
      ("rv_enable_misaligned_access", RVal_Bool false);
      ("rv_ram_base", RVal_Bits (BV 64 0x20000000));
      ("rv_ram_size", RVal_Bits (BV 64 0x20000000));
      ("rv_rom_base", RVal_Bits (BV 64 0x1000));
      ("rv_rom_size", RVal_Bits (BV 64 0x100));
      ("rv_clint_base", RVal_Bits (BV 64 0x2000000));
      ("rv_clint_size", RVal_Bits (BV 64 0xc0000));
      ("rv_htif_tohost", RVal_Bits (BV 64 0x40001000));
      ("cur_privilege", RVal_Enum "Machine");
      ("mstatus", RegVal_Struct [("bits", RVal_Bits (BV 64 0))]);
      ("satp", RVal_Bits (BV 64 0))
    ] ++
    ((fun name => (name, RVal_Bits (BV 64 0x20010000))) <$>
      ["x0"; "x1"; "x2"; "x3"; "x4"; "x5"; "x6"; "x7";
       "x8"; "x9"; "x10"; "x11"; "x12"; "x13"; "x14"; "x15";
       "x16"; "x17"; "x18"; "x19"; "x20"; "x21"; "x22"; "x23";
       "x24"; "x25"; "x26"; "x27"; "x28"; "x29"; "x30"; "x31"]))))))).

Definition executor_test_global : seq_global_state := {|
  seq_instrs := ∅;
  seq_mem := write_mem_list
    (write_mem_list ∅ (BV 64 0x20010000) (replicate 16 (BV 8 0x5a)))
    (BV 64 0x200106d0) (replicate 24 (BV 8 0x5a))
|}.

Definition executor_test_register (regs : reg_map) (name : string) (expected : Z) : bool :=
  match regs !! name with
  | Some (RVal_Bits value) =>
      N.eqb value.(bvn_n) 64 && Z.eqb (bvn_unsigned value) expected
  | _ => false
  end.

Definition ExecutorTest (pc : Z) (trace : isla_trace) (next : Z)
    (register : string) (value : Z) : Prop :=
  (match exec_instr trace (executor_test_regs pc) executor_test_global with
  | Some (regs, _, _, _) =>
      executor_test_register regs "PC" next && executor_test_register regs register value
  | None => false
  end) = true.

Lemma executor_pilot_10190 : ExecutorTest 0x10190 a10190 0x10194 "x5" 0x2401a190.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_10194 : ExecutorTest 0x10194 a10194 0x10198 "x5" (0x2401a0b8 - 216).
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_10198 : ExecutorTest 0x10198 a10198 0x1019c "x10" 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_1019c : ExecutorTest 0x1019c a1019c 0x101a0 "x11" 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_101a0 : ExecutorTest 0x101a0 a101a0 0x156e8 "x1" 0x156e8.
Proof. Time vm_compute. bv_solve. Qed.

Lemma executor_pilot_101d4 : ExecutorTest 0x101d4 a101d4 0x101d8 "x15" 0.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_101d8 : ExecutorTest 0x101d8 a101d8 0x101e0 "x15" 0.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_101dc : ExecutorTest 0x101dc a101dc 0x156e8 "x1" 0x156e8.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_101e0 : ExecutorTest 0x101e0 a101e0 0x101e4 "x13" 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_101e4 : ExecutorTest 0x101e4 a101e4 0x101e8 "x13" 0x5a.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_101e8 : ExecutorTest 0x101e8 a101e8 0x101ec "x14" 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_101ec : ExecutorTest 0x101ec a101ec 0x101f0 "x15" 1.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_101f0 : ExecutorTest 0x101f0 a101f0 0x101f4 "x13" 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_101f4 : ExecutorTest 0x101f4 a101f4 0x101d8 "x1" 0x156e8.
Proof. Time vm_compute. bv_solve. Qed.

Lemma executor_pilot_15694 : ExecutorTest 0x15694 a15694 0x15698 "x10" (0x20010000 + 1744).
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_15698 : ExecutorTest 0x15698 a15698 0x1569c "x12" 48.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_1569c : ExecutorTest 0x1569c a1569c 0x156a0 "x11" 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156a0 : ExecutorTest 0x156a0 a156a0 0x156a4 "x1" 0x106a0.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156a4 : ExecutorTest 0x156a4 a156a4 0x101d4 "x1" 0x156a8.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156a8 : ExecutorTest 0x156a8 a156a8 0x156ac "x10" 0x5a5a5a5a5a5a5a5a.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156ac : ExecutorTest 0x156ac a156ac 0x156b0 "x1" 0x156ac.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156b0 : ExecutorTest 0x156b0 a156b0 0x15d10 "x1" 0x156b4.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156b4 : ExecutorTest 0x156b4 a156b4 0x156b8 "x10" 0x5a5a5a5a5a5a5a5a.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156b8 : ExecutorTest 0x156b8 a156b8 0x156bc "x1" 0x156b8.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156bc : ExecutorTest 0x156bc a156bc 0x15d10 "x1" 0x156c0.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156c0 : ExecutorTest 0x156c0 a156c0 0x156c4 "x11" 20.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156c4 : ExecutorTest 0x156c4 a156c4 0x156c8 "x10" 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156c8 : ExecutorTest 0x156c8 a156c8 0x156cc "x1" 0x106c8.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156cc : ExecutorTest 0x156cc a156cc 0x10190 "x1" 0x156d0.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156d0 : ExecutorTest 0x156d0 a156d0 0x156d4 "x10" 0x5a5a5a5a5a5a5a5a.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156d4 : ExecutorTest 0x156d4 a156d4 0x156d8 "x1" 0x156d4.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156d8 : ExecutorTest 0x156d8 a156d8 0x15d10 "x1" 0x156dc.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156dc : ExecutorTest 0x156dc a156dc 0x156e0 "x8" (0x20010000 + 48).
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156e0 : ExecutorTest 0x156e0 a156e0 0x156e4 "x9" 0.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_156e4 : ExecutorTest 0x156e4 a156e4 0x15694 "x9" 1.
Proof. Time vm_compute. bv_solve. Qed.

Lemma executor_pilot_15d10 : ExecutorTest 0x15d10 a15d10 0x15d14 "x2" (0x20010000 - 16).
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_15d14 : ExecutorTest 0x15d14 a15d14 0x15d18 "x1" 0x156e8.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_15d18 : ExecutorTest 0x15d18 a15d18 0x15d1c "x10" 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_15d1c : ExecutorTest 0x15d1c a15d1c 0x15d20 "x10" 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_15d20 : ExecutorTest 0x15d20 a15d20 0x15d24 "x11" 8.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_15d24 : ExecutorTest 0x15d24 a15d24 0x15d28 "x1" 0xfd24.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_15d28 : ExecutorTest 0x15d28 a15d28 0x10190 "x1" 0x15d2c.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_15d2c : ExecutorTest 0x15d2c a15d2c 0x15d30 "x1" 0x5a5a5a5a5a5a5a5a.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_15d30 : ExecutorTest 0x15d30 a15d30 0x15d34 "x2" (0x20010000 + 16).
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_pilot_15d34 : ExecutorTest 0x15d34 a15d34 0x156e8 "x1" 0x156e8.
Proof. Time vm_compute. bv_solve. Qed.

Print Assumptions executor_pilot_156a8.

Definition ExecutorStoreTest pc trace address len expected : Prop :=
  (match exec_instr trace (executor_test_regs pc) executor_test_global with
  | Some (_, sigma, _, _) =>
      match read_mem sigma.(seq_mem) address len with
      | Some value => Z.eqb (bvn_unsigned value) expected
      | None => false
      end
  | None => false
  end) = true.

Definition ExecutorOutputTest pc trace address expected : Prop :=
  (match exec_instr trace (executor_test_regs pc) executor_test_global with
  | Some (_, _, SWriteMem actual value _ :: _, _) =>
      Z.eqb (bv_unsigned actual) address && Z.eqb (bvn_unsigned value) expected
  | _ => false
  end) = true.

Lemma executor_store_101f0 : ExecutorStoreTest 0x101f0 a101f0 0x20010000 1 0.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_store_15d14 : ExecutorStoreTest 0x15d14 a15d14 0x20010008 8 0x156e8.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_store_15d18 : ExecutorStoreTest 0x15d18 a15d18 0x20010000 8 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_output_10198 : ExecutorOutputTest 0x10198 a10198 0x2401a0c0 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.
Lemma executor_output_1019c : ExecutorOutputTest 0x1019c a1019c 0x2401a0c8 0x20010000.
Proof. Time vm_compute. bv_solve. Qed.

Print Assumptions executor_pilot_10190.
Print Assumptions executor_pilot_10194.
Print Assumptions executor_pilot_10198.
Print Assumptions executor_pilot_1019c.
Print Assumptions executor_pilot_101a0.
Print Assumptions executor_pilot_101d4.
Print Assumptions executor_pilot_101d8.
Print Assumptions executor_pilot_101dc.
Print Assumptions executor_pilot_101e0.
Print Assumptions executor_pilot_101e4.
Print Assumptions executor_pilot_101e8.
Print Assumptions executor_pilot_101ec.
Print Assumptions executor_pilot_101f0.
Print Assumptions executor_pilot_101f4.
Print Assumptions executor_pilot_15694.
Print Assumptions executor_pilot_15698.
Print Assumptions executor_pilot_1569c.
Print Assumptions executor_pilot_156a0.
Print Assumptions executor_pilot_156a4.
Print Assumptions executor_pilot_156ac.
Print Assumptions executor_pilot_156b0.
Print Assumptions executor_pilot_156b4.
Print Assumptions executor_pilot_156b8.
Print Assumptions executor_pilot_156bc.
Print Assumptions executor_pilot_156c0.
Print Assumptions executor_pilot_156c4.
Print Assumptions executor_pilot_156c8.
Print Assumptions executor_pilot_156cc.
Print Assumptions executor_pilot_156d0.
Print Assumptions executor_pilot_156d4.
Print Assumptions executor_pilot_156d8.
Print Assumptions executor_pilot_156dc.
Print Assumptions executor_pilot_156e0.
Print Assumptions executor_pilot_156e4.
Print Assumptions executor_pilot_15d10.
Print Assumptions executor_pilot_15d14.
Print Assumptions executor_pilot_15d18.
Print Assumptions executor_pilot_15d1c.
Print Assumptions executor_pilot_15d20.
Print Assumptions executor_pilot_15d24.
Print Assumptions executor_pilot_15d28.
Print Assumptions executor_pilot_15d2c.
Print Assumptions executor_pilot_15d30.
Print Assumptions executor_pilot_15d34.
Print Assumptions executor_store_101f0.
Print Assumptions executor_store_15d14.
Print Assumptions executor_store_15d18.
Print Assumptions executor_output_10198.
Print Assumptions executor_output_1019c.
