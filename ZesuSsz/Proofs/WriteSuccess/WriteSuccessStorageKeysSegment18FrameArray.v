From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment18FrameDefs.

Lemma write_success_storage_keys_segment18_array
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  writeSuccessStorageKeysLbuPrepared x19 P -∗
  ∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec) (byte : bv 8),
    writeSuccessStorageKeysLbuState P "x1" 0 3 x19 sp pointer base total
      processed remaining bytes tail byte.
Proof.
  iIntros "Hprepared".
  rewrite /writeSuccessStorageKeysLbuPrepared.
  iDestruct "Hprepared" as
    (sp pointer base total processed remaining bytes tail)
    "(Hsys & Hother & HtargetAny & Hx22 & Harray & Houter & %Hlength &
      %Hpointer & %HbaseLower & %HbaseUpper)".
  iPoseProof (write_success_blob_hashes_prepare_lbu_array pointer base
    processed remaining 3 bytes ltac:(lia) with
    "Harray [] [] [] []") as (byte)
    "(Hbyte & Hdone & Hprefix & Hsuffix & %Hlookup & %Hlower & %Hupper)".
  { iPureIntro. exact Hlength. }
  { iPureIntro. exact Hpointer. }
  { iPureIntro. exact HbaseLower. }
  { iPureIntro. exact HbaseUpper. }
  iExists sp, pointer, base, total, processed, remaining, bytes, tail, byte.
  rewrite /writeSuccessStorageKeysLbuState.
  iSplitL "Hsys"; first iExact "Hsys".
  iSplitL "Hother"; first iExact "Hother".
  iSplitL "HtargetAny"; first iExact "HtargetAny".
  iSplitL "Hx22"; first iExact "Hx22".
  iSplitL "Hbyte"; first iExact "Hbyte".
  iSplitL "Hdone"; first iExact "Hdone".
  iSplitL "Hprefix"; first iExact "Hprefix".
  iSplitL "Hsuffix"; first iExact "Hsuffix".
  iSplit; first (iPureIntro; exact Hlookup).
  iSplit; first (iPureIntro; exact Hpointer).
  iSplit; first (iPureIntro; exact Hlower).
  iSplit; first (iPureIntro; exact Hupper).
  iExact "Houter".
Qed.
