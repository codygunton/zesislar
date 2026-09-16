Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.Continuations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesAuthorizationEntry WriteSuccessExactAuthorizationsPrefix
  WriteSuccessExactAuthorizationsCount WriteSuccessExactEncoderU128
  WriteSuccessBlobHashesSpec WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma blob_authorization_region_correct `{!islaG Sigma} `{!threadG}
    sp base total bytes low high count tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_72.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_73.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15564 (writeSuccessBlobHashesLoopExit sp base total bytes
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload low high)
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail))
    (blobAuthorizationCaller sp low high count base total bytes tail P)).
Proof.
  iStartProof. iIntros "#H72 #H73 #Hu128 #Hint #Houtput".
  iAssert (instr_body 0x15564 (∃ oldra old5 : bv 64,
    authorizationPrefixEntry sp low high count oldra old5 tail
      (blobAuthorizationRetained sp base total bytes P))) as "Hprefix".
  { iApply instr_body_exists. iIntros (oldra).
    iApply instr_body_exists. iIntros (old5).
    iApply (authorization_prefix_correct with "H72 H73 Hu128 Hint Houtput"). }
  iApply (instr_pre_wand 0x15564 0x15564 false false with "Hprefix"); [done | done |].
  iIntros "Hexit". iApply blob_exit_to_authorization. iExact "Hexit".
Qed.
Print Assumptions blob_authorization_region_correct.
