Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicRawReturnSpec.
From IslaTraces.write_success_05 Require Import instrs.

Lemma byte_lists_exact_public_raw_count_return_resources
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  byteListsExactPublicRawCountReturnSpec -∗
  byteListsExactPublicCountReturnSpec.
Proof.
  iIntros "#Hcode Hraw".
  iDestruct "Hraw" as
    (sp ret s0 s1 pointer count b12 b13 b14 b15 b16 b17 saved items tail)
    "(%Hfacts & Hresources)".
  destruct Hfacts as
    (Hsaved & Halign & Hmin & Hmax & Hret1 & Hret2 & Hcount & Hlength &
      Hpointer & Hlow & Hhigh).
  iPoseProof (byte_lists_epilogue_pre sp ret s0 s1
    (byteListEndPointer pointer items) saved (bv_unsigned pointer) items tail
    Halign Hmin Hmax Hret1 Hret2 with "Hcode") as "#Hepilogue".
  iEval (unfold byteListsExactPublicRawCountReturn) in "Hresources".
  iApply (byte_lists_public_count_resources_checked sp ret s0 s1 pointer count
    b12 b13 b14 b15 b16 b17 saved items tail with "Hepilogue Hresources");
    assumption.
Qed.
Print Assumptions byte_lists_exact_public_raw_count_return_resources.
