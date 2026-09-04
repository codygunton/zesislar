From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsSpec.

Definition writeSuccessAccessListsTailScratchFrame `{!islaG Sigma}
    (sp : bv 64) (base : Z) (total : nat) : iProp Sigma :=
  (∃ savedX22 : bv 64,
    (bv_unsigned sp + 136) ↦ₘ savedX22 ∗
    (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 base ∗
    (bv_unsigned sp + 264) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
    (bv_unsigned sp + 1744) ↦ₘ? 40 ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    writeSuccessStorageKeysScratch sp ∗ True)%I.

Definition writeSuccessAccessListsTailFrame `{!islaG Sigma} `{!threadG}
    (x19 sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
    (entries processed remaining : list writeSuccessAccessEntry)
    (bytes prefix suffix : list (bv 8)) (x10 x22 x27 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessAccessListsOtherRegShapes ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗ "x19" ↦ᵣ RVal_Bits x19 ∗
   "x22" ↦ᵣ RVal_Bits x22 ∗ "x27" ↦ᵣ RVal_Bits x27 ∗
   base ↦ₘ∗ prefix ∗
   (base + 40 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
   writeSuccessAccessEntriesOwn processed ∗
   writeSuccessAccessEntryOwn entry ∗
   writeSuccessAccessEntriesOwn remaining ∗
   writeSuccessAccessListsTailScratchFrame sp base (length entries) ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessAccessListsEvents sp remaining tail) ∗ P ∗
   writeSuccessAccessListsInvariant sp base entries processed
     (entry :: remaining) bytes prefix suffix ∗
   instr_pre 0x153c0
     (writeSuccessAccessListsLoopExit sp base entries bytes tail x19 P) ∗
   True)%I.

Definition writeSuccessAccessListsAt153b4SplitSpec
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
    iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
      (entries processed remaining : list writeSuccessAccessEntry)
      (bytes prefix suffix : list (bv 8))
      (x10 x11 x22 x27 : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x11" ↦ᵣ RVal_Bits x11 ∗
    (bv_unsigned sp + 272) ↦ₘ
      Z_to_bv 64 (Z.of_nat (length processed)) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    writeSuccessAccessListsTailFrame x19 sp base entry entries processed
      remaining bytes prefix suffix x10 x22 x27 tail P ∗ True)%I.

Definition writeSuccessAccessListsAt153b8Spec
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
    iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
      (entries processed remaining : list writeSuccessAccessEntry)
      (bytes prefix suffix : list (bv 8))
      (x10 x22 x27 : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x11" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (Z.of_nat (length processed))) ∗
    (bv_unsigned sp + 272) ↦ₘ
      Z_to_bv 64 (Z.of_nat (length processed)) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    writeSuccessAccessListsTailFrame x19 sp base entry entries processed
      remaining bytes prefix suffix x10 x22 x27 tail P ∗ True)%I.

Definition writeSuccessAccessListsAt153bcSpec
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
    iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (entry : writeSuccessAccessEntry)
      (entries processed remaining : list writeSuccessAccessEntry)
      (bytes prefix suffix : list (bv 8))
      (x10 x22 x27 : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x11" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (Z.of_nat (length processed)) + BV 64 1)%bv ∗
    (bv_unsigned sp + 272) ↦ₘ
      Z_to_bv 64 (Z.of_nat (length processed)) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    writeSuccessAccessListsTailFrame x19 sp base entry entries processed
      remaining bytes prefix suffix x10 x22 x27 tail P ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessAccessListsAt153b4SplitSpec) := I.
Global Instance : LithiumUnfold (@writeSuccessAccessListsAt153b8Spec) := I.
Global Instance : LithiumUnfold (@writeSuccessAccessListsAt153bcSpec) := I.

Lemma write_success_access_lists_tail_to_153b4
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  writeSuccessAccessListsTailSpec x19 P -∗
  writeSuccessAccessListsAt153b4SplitSpec x19 P.
Proof.
  iIntros "Htail".
  iDestruct "Htail" as
    (sp base entry entries processed remaining bytes prefix suffix
      x10 x11 x22 x27 tail)
    "(Hsys & Hother & Hx2 & Hx10 & Hx19 & Hx11 & Hx22 & Hx27 &
      Hprefix & Hsuffix & Hprocessed & Hentries & Hscratch & Hmmio &
      Htrace & HP & Hinv & Hexit & _)".
  iDestruct "Hentries" as "(Hentry & Hremaining & _)".
  iDestruct "Hscratch" as
    (savedX22)
    "(Hsaved & Hbase & Htotal & Hindex & Hcopied & Houtput & Hstorage & _)".
  iDestruct "Hinv" as
    "(%HentriesEq & %HbytesEq & %HprefixEq & %HsuffixEq & %HbytesSplit &
      %HbytesLength & %HprefixLength & %HsuffixLength & %HentriesBound &
      %Halign & %Hlow & %Hhigh & %HbaseLow & %HbaseHigh & _)".
  iAssert (writeSuccessAccessListsInvariant sp base entries processed
      (entry :: remaining) bytes prefix suffix)%I with "[]" as "Hinv".
  { rewrite /writeSuccessAccessListsInvariant.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iExists sp, base, entry, entries, processed, remaining, bytes, prefix,
    suffix, x10, x11, x22, x27, tail.
  iFrame "Hsys Hx2 Hx11 Hindex".
  iSplit; [iPureIntro; exact Halign |].
  iSplit; [iPureIntro; exact Hlow |].
  iSplit; [iPureIntro; exact Hhigh |].
  rewrite /writeSuccessAccessListsTailFrame
    /writeSuccessAccessListsTailScratchFrame.
  iFrame "Hinv".
  iFrame.
Qed.
