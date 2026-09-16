Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputWhole.

Import ListNotations.

Definition writeOutputExactReturn `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (base : Z) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
   base ↦ₘ∗ bytes ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeOutputExactReturn) := I.

Definition writeOutputExactCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (data size ret : bv 64) (base : Z) (bytes : list (bv 8))
      (tail : spec) (old_x5 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    base ↦ₘ∗ bytes ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents data size
      (take (Z.to_nat (bv_unsigned size))
        (drop (Z.to_nat (bv_unsigned data - base)) bytes)) tail) ∗
    ⌜Z.to_N (bv_unsigned size) =
      N.of_nat (Z.to_nat (bv_unsigned size))⌝ ∗
    ⌜bv_unsigned data =
      (base + Z.of_nat (Z.to_nat (bv_unsigned data - base)))%Z⌝ ∗
    ⌜(Z.to_nat (bv_unsigned data - base) +
      Z.to_nat (bv_unsigned size) <= length bytes)%nat⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    instr_pre (bv_unsigned ret)
      (writeOutputExactReturn data size ret base bytes tail True%I) ∗ True)%I.

Global Instance : LithiumUnfold (@writeOutputExactCallSpec) := I.

Lemma write_output_exact_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190 writeOutputExactCallSpec.
Proof.
  iStartProof. iIntros "#Hcode". rewrite instr_pre'_eq.
  iIntros "Hentry". iDestruct "Hentry" as
    (data size ret base bytes tail old_x5)
    "(Hsys & H1 & H5 & H10 & H11 & Hbytes & Hmmio & Htrace &
      %Hsize & %Hdata & %Hrange & %Hret0 & %Hret1 & %Hret2 &
      Hreturn & _)".
  iPoseProof (write_output_whole_correct data size ret base
    (Z.to_nat (bv_unsigned data - base))
    (Z.to_nat (bv_unsigned size)) bytes tail True%I with "Hcode") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody". iApply "Hbody".
  iExists old_x5. iFrame.
  repeat iSplit; iPureIntro; assumption.
Qed.

Print Assumptions write_output_exact_call_correct.

Lemma write_output_whole_entry_to_exact `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (base : Z) (start count : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  writeOutputWholeSpec data size ret base start count bytes tail P -∗
  writeOutputExactCallSpec.
Proof.
  iStartProof. iIntros "Hentry".
  iDestruct "Hentry" as (old_x5)
    "(Hsys & H1 & H5 & H10 & H11 & Hbytes & Hmmio & Htrace &
      %Hsize & %Hdata & %Hrange & %Hret0 & %Hret1 & %Hret2 &
      HP & Hreturn & _)".
  have Hstart : Z.to_nat (bv_unsigned data - base) = start.
  { rewrite Hdata. replace (base + Z.of_nat start - base)%Z with
      (Z.of_nat start) by lia. apply Nat2Z.id. }
  have Hcount := f_equal N.to_nat Hsize.
  rewrite Z_N_nat Nat2N.id in Hcount.
  subst start count.
  iExists data, size, ret, base, bytes, tail, old_x5.
  iFrame "Hsys H1 H5 H10 H11 Hbytes Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption.
  2: done.
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hreturn"); [done | done |].
  rewrite /writeOutputExactReturn.
  iIntros "(Hsys & H1 & H5 & H10 & H11 & Hbytes & Hmmio & Htrace & _)".
  iFrame.
Qed.

Lemma write_output_whole_body_from_exact `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (base : Z) (start count : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_body 0x10190 writeOutputExactCallSpec -∗
  instr_body 0x10190
    (writeOutputWholeSpec data size ret base start count bytes tail P).
Proof.
  iStartProof. iIntros "Hbody".
  iApply (instr_pre_wand 0x10190 0x10190 false false with "Hbody");
    [done | done |].
  iApply write_output_whole_entry_to_exact.
Qed.

Print Assumptions write_output_whole_body_from_exact.

Lemma write_output_whole_correct_from_exact `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (base : Z) (start count : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190
    (writeOutputWholeSpec data size ret base start count bytes tail P).
Proof.
  iStartProof. iIntros "Hcode".
  iApply write_output_whole_body_from_exact.
  iApply write_output_exact_call_correct. iExact "Hcode".
Qed.

Print Assumptions write_output_whole_correct_from_exact.
