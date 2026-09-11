Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.

Lemma write_success_blob_hashes_segment17_return_15490
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  writeSuccessBlobHashesLbuResult P "x22" 19 1 sp pointer base total
    processed remaining bytes tail byte -∗
  writeSuccessBlobHashesBodySpec P.
Proof.
  iIntros "Hresult".
  rewrite /writeSuccessBlobHashesLbuResult.
  iDestruct "Hresult" as
    "(Hsys & Hother & Hx22 & Hx19 & Hbyte & Hdone & Hprefix & Hsuffix &
      %Hlookup & %Hpointer & Houter)".
  iPoseProof (write_success_blob_hashes_segment15_recombine_lbu pointer
    base processed 1 bytes byte with
    "[] [] Hdone Hbyte Hprefix Hsuffix") as "Harray".
  { iPureIntro. exact Hpointer. }
  { iPureIntro. exact Hlookup. }
  iPoseProof (write_success_blob_hashes_segment15_registers "x22" 19 byte
    ltac:(vm_compute; reflexivity) with "Hother Hx22") as "Hother".
  iEval (unfold writeSuccessBlobHashesLbuOuterFrame) in "Houter".
  iDestruct "Houter" as
    "(Hx2 & Hx27 & Hscratch & Hmmio & Hevents & HP & Hinv & Hexit & _)".
  rewrite /writeSuccessBlobHashesBodySpec.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iFrame "Hsys Hother Hx19 Harray Hx2 Hx27 Hscratch Hmmio Hevents HP Hinv
    Hexit".
Qed.
