Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTactics.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64NoneBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64NoneEntryRaw.

Lemma zesu_encoder_optional_u64_none_entry
    `{!islaG Sigma} `{!threadG} :
  instr 0x15bc8 (Some a15bc8) -∗
  instr 0x15bcc (Some a15bcc) -∗
  instr_body 0x15c04 zesuEncoderOptionalU64NoneAtTail -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64NoneCallSpec.
Proof.
  iStartProof. iIntros "#Hc8 #Hcc Htail".
  iPoseProof (zesu_encoder_optional_u64_none_tail_body_adapter with "Htail")
    as "HpublicTail".
  iPoseProof (zesu_encoder_optional_u64_none_entry_raw with
    "Hc8 Hcc HpublicTail") as "Hbody".
  iExact "Hbody".
Qed.
