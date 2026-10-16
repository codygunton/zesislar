Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.AltFlFreeBlockEntries.
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Require Import ZesuSsz.Compliance.FreeSizeClassLeafFacts.
Require Import ZesuSsz.Compliance.FreeSizeClassIteFacts.
Require Import ZesuSsz.Compliance.FreeClassFacts.

Lemma freeClassDominatesCandidate args (classWord alignmentWord : bv 64) :
  classWord = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) ->
  alignmentWord = freeAlignmentWord args ->
  bv_unsigned alignmentWord < bv_unsigned classWord ->
  freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args.
Proof.
  intros Hclass Hword Hguard.
  pose proof (freeSizeClassOfBytesRange (freeBufferLength args)) as Hrange.
  assert (Hfits : 0 <= freeSizeClassOfBytes (freeBufferLength args) < bv_modulus 64).
  { unfold bv_modulus. cbn. lia. }
  rewrite Hclass Hword (Z_to_bv_small 64 _ Hfits) in Hguard.
  unfold freeCandidateClass. symmetry. apply Z.max_l. lia.
Qed.

Lemma freeEntry41f7cLeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80041f7c args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (0 <= freeBufferLength args <= 8 -> freeSizeClassOfBytes (freeBufferLength args) = 0) /\
    (9 <= freeBufferLength args <= 16 -> freeSizeClassOfBytes (freeBufferLength args) = 1) /\
    (0 <= freeBufferLength args <= 16 ->
      freeSizeClassOfBytes (freeBufferLength args) =
        if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (freeBufferLength args))) (@bv_signed 128 (@BV 128 9 I))) then 0 else 1)⌝.
Proof.
unfold freeEntryAt80041f7c.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (conj (freeSizeClassLeaf0 (freeBufferLength args)) (conj (freeSizeClassLeaf1 (freeBufferLength args)) (freeSizeClassIte41f7c (freeBufferLength args))))))))).
Qed.

Lemma freeEntry41fb4LeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80041fb4 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (2049 <= freeBufferLength args <= 4096 -> freeSizeClassOfBytes (freeBufferLength args) = 9)⌝.
Proof.
unfold freeEntryAt80041fb4.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (freeSizeClassLeaf9 (freeBufferLength args))))))).
Qed.

Lemma freeEntry41fd8LeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80041fd8 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (65 <= freeBufferLength args <= 128 -> freeSizeClassOfBytes (freeBufferLength args) = 4)⌝.
Proof.
unfold freeEntryAt80041fd8.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (freeSizeClassLeaf4 (freeBufferLength args))))))).
Qed.

Lemma freeEntry42010LeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80042010 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (262145 <= freeBufferLength args <= 524288 -> freeSizeClassOfBytes (freeBufferLength args) = 16) /\
    (524289 <= freeBufferLength args <= 1048576 -> freeSizeClassOfBytes (freeBufferLength args) = 17) /\
    (262145 <= freeBufferLength args <= 1048576 ->
      freeSizeClassOfBytes (freeBufferLength args) =
        if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (freeBufferLength args))) (@bv_unsigned 64 (@BV 64 524289 I))) then 16 else 17)⌝.
Proof.
unfold freeEntryAt80042010.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (conj (freeSizeClassLeaf16 (freeBufferLength args)) (conj (freeSizeClassLeaf17 (freeBufferLength args)) (freeSizeClassIte42010 (freeBufferLength args))))))))).
Qed.

Lemma freeEntry42028LeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80042028 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (17 <= freeBufferLength args <= 32 -> freeSizeClassOfBytes (freeBufferLength args) = 2) /\
    (33 <= freeBufferLength args <= 64 -> freeSizeClassOfBytes (freeBufferLength args) = 3) /\
    (17 <= freeBufferLength args <= 64 ->
      freeSizeClassOfBytes (freeBufferLength args) =
        if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (freeBufferLength args))) (@bv_signed 128 (@BV 128 33 I))) then 2 else 3)⌝.
Proof.
unfold freeEntryAt80042028.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (conj (freeSizeClassLeaf2 (freeBufferLength args)) (conj (freeSizeClassLeaf3 (freeBufferLength args)) (freeSizeClassIte42028 (freeBufferLength args))))))))).
Qed.

Lemma freeEntry42054LeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80042054 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (16385 <= freeBufferLength args <= 32768 -> freeSizeClassOfBytes (freeBufferLength args) = 12) /\
    (32769 <= freeBufferLength args <= 65536 -> freeSizeClassOfBytes (freeBufferLength args) = 13) /\
    (16385 <= freeBufferLength args <= 65536 ->
      freeSizeClassOfBytes (freeBufferLength args) =
        if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (freeBufferLength args))) (@bv_unsigned 64 (@BV 64 32769 I))) then 12 else 13)⌝.
Proof.
unfold freeEntryAt80042054.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (conj (freeSizeClassLeaf12 (freeBufferLength args)) (conj (freeSizeClassLeaf13 (freeBufferLength args)) (freeSizeClassIte42054 (freeBufferLength args))))))))).
Qed.

Lemma freeEntry42070LeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80042070 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (513 <= freeBufferLength args <= 1024 -> freeSizeClassOfBytes (freeBufferLength args) = 7) /\
    (1025 <= freeBufferLength args <= 2048 -> freeSizeClassOfBytes (freeBufferLength args) = 8) /\
    (513 <= freeBufferLength args <= 2048 ->
      freeSizeClassOfBytes (freeBufferLength args) =
        if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (freeBufferLength args))) (@bv_signed 128 (@BV 128 1025 I))) then 7 else 8)⌝.
Proof.
unfold freeEntryAt80042070.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (conj (freeSizeClassLeaf7 (freeBufferLength args)) (conj (freeSizeClassLeaf8 (freeBufferLength args)) (freeSizeClassIte42070 (freeBufferLength args))))))))).
Qed.

Lemma freeEntry42090LeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt80042090 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (4194305 <= freeBufferLength args <= 8388608 -> freeSizeClassOfBytes (freeBufferLength args) = 20)⌝.
Proof.
unfold freeEntryAt80042090.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (freeSizeClassLeaf20 (freeBufferLength args))))))).
Qed.

Lemma freeEntry420b0LeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt800420b0 args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (4097 <= freeBufferLength args <= 8192 -> freeSizeClassOfBytes (freeBufferLength args) = 10) /\
    (8193 <= freeBufferLength args <= 16384 -> freeSizeClassOfBytes (freeBufferLength args) = 11) /\
    (4097 <= freeBufferLength args <= 16384 ->
      freeSizeClassOfBytes (freeBufferLength args) =
        if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (freeBufferLength args))) (@bv_unsigned 64 (@BV 64 8193 I))) then 10 else 11)⌝.
Proof.
unfold freeEntryAt800420b0.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (conj (freeSizeClassLeaf10 (freeBufferLength args)) (conj (freeSizeClassLeaf11 (freeBufferLength args)) (freeSizeClassIte420b0 (freeBufferLength args))))))))).
Qed.

Lemma freeEntry420ccLeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt800420cc args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (129 <= freeBufferLength args <= 256 -> freeSizeClassOfBytes (freeBufferLength args) = 5) /\
    (257 <= freeBufferLength args <= 512 -> freeSizeClassOfBytes (freeBufferLength args) = 6) /\
    (129 <= freeBufferLength args <= 512 ->
      freeSizeClassOfBytes (freeBufferLength args) =
        if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (freeBufferLength args))) (@bv_signed 128 (@BV 128 257 I))) then 5 else 6)⌝.
Proof.
unfold freeEntryAt800420cc.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (conj (freeSizeClassLeaf5 (freeBufferLength args)) (conj (freeSizeClassLeaf6 (freeBufferLength args)) (freeSizeClassIte420cc (freeBufferLength args))))))))).
Qed.

Lemma freeEntry420ecLeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt800420ec args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (1048577 <= freeBufferLength args <= 2097152 -> freeSizeClassOfBytes (freeBufferLength args) = 18) /\
    (2097153 <= freeBufferLength args <= 4194304 -> freeSizeClassOfBytes (freeBufferLength args) = 19) /\
    (1048577 <= freeBufferLength args <= 4194304 ->
      freeSizeClassOfBytes (freeBufferLength args) =
        if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (freeBufferLength args))) (@bv_unsigned 64 (@BV 64 2097153 I))) then 18 else 19)⌝.
Proof.
unfold freeEntryAt800420ec.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (conj (freeSizeClassLeaf18 (freeBufferLength args)) (conj (freeSizeClassLeaf19 (freeBufferLength args)) (freeSizeClassIte420ec (freeBufferLength args))))))))).
Qed.

Lemma freeEntry4210cLeafIntroduction `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeEntryAt8004210c args x1 x2 x8 x10 x11 x12 x13 x14 bufferBytes listBytes frameBytes ⊢
  ⌜x12 = Z_to_bv 64 (freeSizeClassOfBytes (freeBufferLength args)) /\
    x13 = x12 /\
    x14 = freeAlignmentWord args /\
    bv_unsigned x14 < bv_unsigned x12 /\
    freeSizeClassOfBytes (freeBufferLength args) = freeCandidateClass args /\
    (65537 <= freeBufferLength args <= 131072 -> freeSizeClassOfBytes (freeBufferLength args) = 14) /\
    (131073 <= freeBufferLength args <= 262144 -> freeSizeClassOfBytes (freeBufferLength args) = 15) /\
    (65537 <= freeBufferLength args <= 262144 ->
      freeSizeClassOfBytes (freeBufferLength args) =
        if bool_decide (Z.lt (@bv_unsigned 64 (Z_to_bv 64 (freeBufferLength args))) (@bv_unsigned 64 (@BV 64 131073 I))) then 14 else 15)⌝.
Proof.
unfold freeEntryAt8004210c.
iIntros "(_ & %Hbranch)".
iPureIntro. unfold freeBlockFacts in Hbranch.
destruct Hbranch as (_ & Hclass & Hcopy & Hword & Hguard).
exact (conj Hclass (conj Hcopy (conj Hword (conj Hguard (conj (freeClassDominatesCandidate args x12 x14 Hclass Hword Hguard) (conj (freeSizeClassLeaf14 (freeBufferLength args)) (conj (freeSizeClassLeaf15 (freeBufferLength args)) (freeSizeClassIte4210c (freeBufferLength args))))))))).
Qed.
