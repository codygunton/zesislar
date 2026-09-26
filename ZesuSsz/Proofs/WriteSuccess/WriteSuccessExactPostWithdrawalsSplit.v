Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From IslaTraces.write_success_blocks Require Import Index.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation
  WriteSuccessValueSpec WriteSuccessOutputSemantic WriteSuccessPostTransactionDescriptors.

(* The second integer call has not executed at this boundary.
   The first exact payload has been consumed; its exact tail remains. *)
Definition writeSuccessExactPostWithdrawals156fcRegisters
    `{!islaG Sigma} `{!threadG} {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x156f8) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (writeSuccessValueWord (writeSuccessValues witness) 14) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x12"; "x13"; "x14"; "x15"]) ∗
   "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
   "x8" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (bv_unsigned (writeSuccessWithdrawalsBase witness) +
       Z.of_nat (length (writeSuccessWithdrawalsBytes witness)))) ∗
   "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗ True)%I.
Global Instance : LithiumUnfold
  (@writeSuccessExactPostWithdrawals156fcRegisters) := I.

Definition writeSuccessExactPostWithdrawalsAt156fc
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  (writeSuccessExactPostWithdrawals156fcRegisters witness ∗
   writeSuccessExactPostWithdrawalsUntouched
     (bv_unsigned (writeSuccessWithdrawalsBase witness))
     (writeSuccessWithdrawalsBytes witness)
     (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P) ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (exactPostWithdrawalsFirstTail witness) ∗ True)%I.
Global Instance : LithiumUnfold
  (@writeSuccessExactPostWithdrawalsAt156fc) := I.

(* This local exit is copied from the frozen draft, without changing
   the suffix-hashes interface or its continuation. *)
Definition writeSuccessExactPostWithdrawalsSplit1573cEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  let descriptors := writeSuccessPost1573cDescriptors
    (writeSuccessFrameSp witness) (writeSuccessPostData witness) in
  writeOutputPayloadsSpec descriptors
    (writeSuccessExactPostPayloadsAt descriptors witness)
    (writeSuccessTraceTail witness).

Definition writeSuccessExactPostWithdrawalsSplitExitFrame
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x1"; "x5"; "x9"; "x11"; "x12"; "x13"; "x14"; "x15"; "x18"]) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗
     writeSuccessWithdrawalsBytes witness ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactPostWithdrawalsSplit1573cEvents witness) ∗
   writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P ∗ True)%I.
Global Instance : LithiumUnfold
  (@writeSuccessExactPostWithdrawalsSplitExitFrame) := I.

(* Phase C must discharge both explicit obligations. No segment proof
   follows merely from this composition lemma. *)
Lemma write_success_exact_post_withdrawals_from_split
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  (instr_body 0x156fc (writeSuccessExactPostWithdrawalsAt156fc args witness P) -∗
   instr_body 0x156e8
     (writeSuccessExactPostWithdrawalsBoundary
       (writeSuccessFrameSp witness)
       (bv_unsigned (writeSuccessWithdrawalsBase witness))
       (writeSuccessWithdrawalsBytes witness)
       (writeSuccessExactPostWithdrawalsEvents witness)
       (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P))) -∗
  (instr_body 0x15744
     (writeSuccessSuffixHashesBoundary
       (fun _ => writeSuccessExactPostWithdrawalsSplitExitFrame args witness P)) -∗
   instr_body 0x156fc (writeSuccessExactPostWithdrawalsAt156fc args witness P)) -∗
  instr_body 0x15744
    (writeSuccessSuffixHashesBoundary
      (fun _ => writeSuccessExactPostWithdrawalsSplitExitFrame args witness P)) -∗
  instr_body 0x156e8
    (writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)).
Proof.
  iIntros "Hprefix Hsuffix Hexit".
  iApply "Hprefix". iApply "Hsuffix". iExact "Hexit".
Qed.

Print Assumptions write_success_exact_post_withdrawals_from_split.
