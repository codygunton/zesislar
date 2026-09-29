Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsPayloadJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.

Local Transparent tailFieldsActivePayloads.

Lemma tail_fields_15910_payload_handoff `{!islaG Sigma}
    (decoded : list (bv 8)) (data : WriteSuccessPostTransactionData) :
  tailFieldsActivePayloads decoded data -∗
  writeSuccessDescriptorResources (writeSuccessPostBytes15910 data)
    (writeSuccessPostBytes15910Payload data) ∗
  (writeSuccessDescriptorResources (writeSuccessPostBytes15910 data)
    (writeSuccessPostBytes15910Payload data) -∗
   tailFieldsActivePayloads decoded data).
Proof.
  rewrite /tailFieldsActivePayloads.
  iIntros "(Hfirst & Hsecond & Hthird & Hfourth & Hlist1 & Hlist2 & Hlist3 & _)".
  iFrame "Hthird".
  iIntros "Hthird". iFrame.
Qed.
Print Assumptions tail_fields_15910_payload_handoff.

Lemma tail_fields_15920_payload_handoff `{!islaG Sigma}
    (decoded : list (bv 8)) (data : WriteSuccessPostTransactionData) :
  tailFieldsActivePayloads decoded data -∗
  writeSuccessDescriptorResources (writeSuccessPostBytes15920 data)
    (writeSuccessPostBytes15920Payload data) ∗
  (writeSuccessDescriptorResources (writeSuccessPostBytes15920 data)
    (writeSuccessPostBytes15920Payload data) -∗
   tailFieldsActivePayloads decoded data).
Proof.
  rewrite /tailFieldsActivePayloads.
  iIntros "(Hfirst & Hsecond & Hthird & Hfourth & Hlist1 & Hlist2 & Hlist3 & _)".
  iFrame "Hfourth".
  iIntros "Hfourth". iFrame.
Qed.
Print Assumptions tail_fields_15920_payload_handoff.
