From IslaTraces.write_success_blocks Require Import Index.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBytesCall.

Require Import ZesuSsz.Experiments.WriteSuccessNativeSuffixBytes158e0Carrier.

Lemma write_success_native_suffix_bytes_carrier_158e0_to_158f0
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x158f0
    (writeSuccessSuffixBytesAt158f0Carrier sp P) -∗
  instr_body 0x158e0
    (writeSuccessSuffixBytesAt158e0Carrier sp P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hbytes Hnext".
  iApply (write_success_suffix_bytes_158e0_carrier sp P
    with "Hlookup Hcode Hbytes").
  iExact "Hnext".
Qed.
