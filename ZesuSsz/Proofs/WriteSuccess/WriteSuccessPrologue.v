From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_00 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueChunk14d30.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueChunk14d48.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueChunk14d5c.

Lemma write_success_prologue `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_00.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14d30
    (write_success_prologue_entry sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7
       s8 s9 s10 s11 P ∗
     instr_pre 0x14d7c
       (write_success_prologue_exit sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7
          s8 s9 s10 s11 P) ∗ True).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hcode".
  iApply (write_success_prologue_chunk_14d30 with "Hcode").
  iApply (write_success_prologue_chunk_14d48 with "Hcode").
  iApply (write_success_prologue_chunk_14d5c with "Hcode").
Qed.
