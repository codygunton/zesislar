From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints
  InstrSpecs.Lookup.find_in_context_instr_body_lookup_resources_inst
  : typeclass_instances.

Definition writeSuccessHeaderRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessHeaderRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessHeaderRegisters.

Definition writeSuccessHeaderEvent (data size : bv 64) (tail : spec) : spec :=
  scons (SWriteMem (BV 64 0x2401a0c0) data)
    (scons (SWriteMem (BV 64 0x2401a0c8) size) tail).

Definition writeSuccessHeaderEvents (sp : bv 64) (tail : spec) : spec :=
  writeSuccessHeaderEvent (BV 64 0x179c5) (BV 64 6)
    (writeSuccessHeaderEvent (sp + 1184)%bv (BV 64 32)
      (writeSuccessHeaderEvent (sp + 1216)%bv (BV 64 20)
        (writeSuccessHeaderEvent (sp + 1236)%bv (BV 64 32)
          (writeSuccessHeaderEvent (sp + 1268)%bv (BV 64 32)
            (writeSuccessHeaderEvent (sp + 1300)%bv (BV 64 256)
              (writeSuccessHeaderEvent (sp + 1556)%bv (BV 64 32)
                tail)))))).

Definition writeSuccessHeaderPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessHeaderRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 104) ↦ₘ? 16 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes ∗
   (bv_unsigned sp + 1624) ↦ₘ? 272 ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Definition writeSuccessHeaderSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessHeaderRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    (bv_unsigned sp + 104) ↦ₘ? 16 ∗
    (bv_unsigned sp + 312) ↦ₘ∗ bytes ∗
    (bv_unsigned sp + 1032) ↦ₘ? 864 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessHeaderEvents sp tail) ∗
    ⌜length bytes = 720%nat⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    P ∗ instr_pre 0x14e88 (writeSuccessHeaderPost sp bytes tail P))%I.

Local Instance : LithiumUnfold (@writeSuccessHeaderSpec) := I.
Local Instance : LithiumUnfold (@writeSuccessHeaderPost) := I.

Ltac run_write_success_header :=
  lazymatch goal with
  | |- instr_body 0x14e88 _ => idtac
  | _ =>
      first
        [ progress iEval (unfold zesuMemcpyCallSpec, zesu_c_call)
        | progress iEval (unfold zesuWriteOutputCallSpec, zesu_c_call)
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | bv_solve
        | lia ];
      run_write_success_header
  end.

Lemma write_success_header_block `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x14e00 (writeSuccessHeaderSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hmemcpy #Houtput".
  run_write_success_header.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
Qed.
