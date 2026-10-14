Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.MemoryAccess.
Require Import isla.riscv64.riscv64.
From Coq Require Import List Lia.
Import ListNotations.

Local Open Scope Z_scope.
Lemma memory_access_opt_in : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepMemoryAccess) in idtac.
  exact I.
Qed.

Section memory_access_off.
Context `{!islaG Sigma} `{!threadG}.

Lemma memory_access_switch_off (base offset : Z) (bytes : list (bv 8))
    (value : bv 8) kind tag (tail : isla_trace)
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hextent : offset + 1 <= Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hgoal".
  Fail zesu_memory_access_if_enabled ltac:(idtac).
  iExact "Hgoal".
Qed.

End memory_access_off.

Require Import ZesuSsz.Automation.Switches.MemoryAccess.

Section memory_access_tests.
Context `{!islaG Sigma} `{!threadG}.

Lemma memory_write_one_byte (base offset : Z) (bytes : list (bv 8))
    (value : bv 8) kind tag (tail : isla_trace)
    (Hbase : 0 <= base)
    (Hoffset : 0 <= offset)
    (Hextent : offset + 1 <= Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  (base ↦ₘ∗ <[Z.to_nat offset := value]> bytes -∗ WPasm tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hcontinue".
  zesu_memory_access_if_enabled ltac:(idtac).
  by iApply "Hcontinue".
Qed.

Lemma memory_write_two_bytes (base offset : Z) (bytes : list (bv 8))
    (value : bv 16) kind tag (tail : isla_trace)
    (Hbase : 0 <= base)
    (Hoffset : 0 <= offset)
    (Hextent : offset + 2 <= Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  (base ↦ₘ∗ (take (Z.to_nat offset) bytes ++
    bv_to_little_endian 2 8 (bv_unsigned value) ++
    drop (Z.to_nat offset + 2) bytes) -∗ WPasm tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 2 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hcontinue".
  zesu_memory_access_if_enabled ltac:(idtac).
  by iApply "Hcontinue".
Qed.

Lemma memory_write_eight_bytes_symbolic (base constant : Z)
    (index value : bv 64) (bytes : list (bv 8)) kind tag (tail : isla_trace)
    (Hbase : 0 <= base)
    (Hoffset : 0 <= bv_unsigned index * 8 + constant)
    (Hextent : bv_unsigned index * 8 + constant + 8 <= Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  (base ↦ₘ∗ (take (Z.to_nat (bv_unsigned index * 8 + constant)) bytes ++
    bv_to_little_endian 8 8 (bv_unsigned value) ++
    drop (Z.to_nat (bv_unsigned index * 8 + constant) + 8) bytes) -∗
    WPasm tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add
      (bv_add (Z_to_bv 64 base) (bv_mul index (Z_to_bv 64 8)))
      (Z_to_bv 64 constant))))
    (RVal_Bits (bv_to_bvn value)) 8 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hcontinue".
  zesu_memory_access_if_enabled ltac:(idtac).
  by iApply "Hcontinue".
Qed.

Lemma memory_read_one_byte (base offset : Z) (bytes : list (bv 8))
    (read_value : bv 8) kind tag (tail : isla_trace)
    (Hbase : 0 <= base)
    (Hoffset : 0 <= offset)
    (Hextent : offset + 1 <= Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  (∀ value : bv 8,
    ⌜bytes !! Z.to_nat offset = Some value⌝ -∗
    ⌜read_value = value⌝ -∗ base ↦ₘ∗ bytes -∗ WPasm tail) -∗
  WPasm (ReadMem (RVal_Bits (bv_to_bvn read_value)) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    1 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hcontinue".
  zesu_memory_access_if_enabled ltac:(idtac).
  iIntros (value Hvalue Hread) "Hbytes".
  iApply ("Hcontinue" with "[] [] Hbytes"); done.
Qed.

Lemma memory_read_two_bytes (base offset : Z) (bytes : list (bv 8))
    (read_value : bv 16) kind tag (tail : isla_trace)
    (Hbase : 0 <= base)
    (Hoffset : 0 <= offset)
    (Hextent : offset + 2 <= Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  (∀ value : bv 16,
    ⌜value = Z_to_bv 16 (little_endian_to_bv 8
      (take 2 (drop (Z.to_nat offset) bytes)))⌝ -∗
    ⌜read_value = value⌝ -∗ base ↦ₘ∗ bytes -∗ WPasm tail) -∗
  WPasm (ReadMem (RVal_Bits (bv_to_bvn read_value)) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    2 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hcontinue".
  zesu_memory_access_if_enabled ltac:(idtac).
  iIntros (value Hvalue Hread) "Hbytes".
  iApply ("Hcontinue" with "[] [] Hbytes"); done.
Qed.

Lemma memory_read_eight_bytes (base offset : Z) (bytes : list (bv 8))
    (read_value : bv 64) kind tag (tail : isla_trace)
    (Hbase : 0 <= base)
    (Hoffset : 0 <= offset)
    (Hextent : offset + 8 <= Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  (∀ value : bv 64,
    ⌜value = Z_to_bv 64 (little_endian_to_bv 8
      (take 8 (drop (Z.to_nat offset) bytes)))⌝ -∗
    ⌜read_value = value⌝ -∗ base ↦ₘ∗ bytes -∗ WPasm tail) -∗
  WPasm (ReadMem (RVal_Bits (bv_to_bvn read_value)) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    8 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hcontinue".
  zesu_memory_access_if_enabled ltac:(idtac).
  iIntros (value Hvalue Hread) "Hbytes".
  iApply ("Hcontinue" with "[] [] Hbytes"); done.
Qed.

Lemma memory_duplicate_base_rejects (base offset : Z)
    (left right : list (bv 8)) (value : bv 8) kind tag (tail : isla_trace)
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hextent : offset + 1 <= Z.of_nat (length left))
    (Hnowrap : base + Z.of_nat (length left) <= 2 ^ 64) :
  base ↦ₘ∗ left -∗ base ↦ₘ∗ right -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail).
Proof.
  iIntros "Hleft Hright Hgoal".
  Fail zesu_memory_access_if_enabled ltac:(idtac).
  iExact "Hgoal".
Qed.

Lemma memory_missing_bound_rejects (base offset : Z) (bytes : list (bv 8))
    (value : bv 8) kind tag (tail : isla_trace) :
  base ↦ₘ∗ bytes -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hgoal".
  Fail zesu_memory_access_if_enabled ltac:(idtac).
  iExact "Hgoal".
Qed.

Lemma memory_write_end_at_modulus (base : Z) (bytes : list (bv 8))
    (value : bv 64) kind tag (tail : isla_trace)
    (Hbase : 0 <= base)
    (Hlength : length bytes = 8%nat)
    (Hend : base + 8 = 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  (base ↦ₘ∗ (take (Z.to_nat 0) bytes ++
    bv_to_little_endian 8 8 (bv_unsigned value) ++
    drop (Z.to_nat 0 + 8) bytes) -∗ WPasm tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 0))))
    (RVal_Bits (bv_to_bvn value)) 8 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hcontinue".
  zesu_memory_access_if_enabled ltac:(idtac).
  by iApply "Hcontinue".
Qed.

Lemma memory_write_distinct_bases (base other offset : Z) (bytes otherBytes : list (bv 8))
    (value : bv 16) (Hdifferent : base <> other) kind tag (tail : isla_trace)
    (Hbase : 0 <= base)
    (Hoffset : 0 <= offset)
    (Hextent : offset + 2 <= Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  other ↦ₘ∗ otherBytes -∗ base ↦ₘ∗ bytes -∗
  (base ↦ₘ∗ (take (Z.to_nat offset) bytes ++
    bv_to_little_endian 2 8 (bv_unsigned value) ++
    drop (Z.to_nat offset + 2) bytes) -∗ other ↦ₘ∗ otherBytes -∗ WPasm tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 2 tag Mk_annot :t: tail).
Proof.
  iIntros "Hother Hbytes Hcontinue".
  zesu_memory_access_if_enabled ltac:(idtac).
  iIntros "Hupdated".
  iApply ("Hcontinue" with "Hupdated Hother").
Qed.

Lemma memory_one_past_end_rejects (base offset : Z) (bytes : list (bv 8))
    (value : bv 8) kind tag (tail : isla_trace)
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hend : offset = Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hgoal".
  Fail zesu_memory_access_if_enabled ltac:(idtac).
  iExact "Hgoal".
Qed.

Lemma memory_wrapping_address_rejects (base offset : Z) (bytes : list (bv 8))
    (value : bv 8) kind tag (tail : isla_trace)
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hextent : offset + 1 <= Z.of_nat (length bytes))
    (Hwrap : 2 ^ 64 <= base + offset) :
  base ↦ₘ∗ bytes -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hgoal".
  Fail zesu_memory_access_if_enabled ltac:(idtac).
  iExact "Hgoal".
Qed.

Lemma memory_write_literal_offset (base : Z) (bytes : list (bv 8))
    (value : bv 16) kind tag (tail : isla_trace)
    (Hbase : 0 <= base)
    (H12 : 0 <= 12)
    (Hextent : 12 + 2 <= Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  (base ↦ₘ∗ (take (Z.to_nat 12) bytes ++
    bv_to_little_endian 2 8 (bv_unsigned value) ++
    drop (Z.to_nat 12 + 2) bytes) -∗ WPasm tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 12))))
    (RVal_Bits (bv_to_bvn value)) 2 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hcontinue".
  zesu_memory_access_if_enabled ltac:(idtac).
  by iApply "Hcontinue".
Qed.

Lemma memory_write_updated_image (base : Z) (bytes : list (bv 8))
    (value : bv 16) (previous : bv 8) kind tag (tail : isla_trace)
    (Hbase : 0 <= base)
    (H12 : 0 <= 12)
    (Hextent : 12 + 2 <= Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  base ↦ₘ∗ <[3%nat := previous]> bytes -∗
  (base ↦ₘ∗ (take (Z.to_nat 12) (<[3%nat := previous]> bytes) ++
    bv_to_little_endian 2 8 (bv_unsigned value) ++
    drop (Z.to_nat 12 + 2) (<[3%nat := previous]> bytes)) -∗ WPasm tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 12))))
    (RVal_Bits (bv_to_bvn value)) 2 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hcontinue".
  zesu_memory_access_if_enabled ltac:(idtac).
  by iApply "Hcontinue".
Qed.

Lemma memory_write_preserves_peer_and_shelf (base offset : Z) (bytes : list (bv 8))
    (value : bv 8) kind tag (tail : isla_trace)
    (Hbase : 0 <= base)
    (Hoffset : 0 <= offset)
    (Hextent : offset + 1 <= Z.of_nat (length bytes))
    (Hnowrap : base + Z.of_nat (length bytes) <= 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  (base ↦ₘ∗ <[Z.to_nat offset := value]> bytes -∗ WPasm tail) -∗
  WPasm (WriteMem (RVal_Bool true) kind
    (RVal_Bits (bv_to_bvn (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (RVal_Bits (bv_to_bvn value)) 1 tag Mk_annot :t: tail).
Proof.
  iIntros "Hbytes Hcontinue".
  assert (unrelated : nat) by shelve.
  assert (Hpeer : True).
  2: zesu_memory_access_if_enabled ltac:(idtac).
  2: by iApply "Hcontinue".
  exact I.
  Unshelve.
  exact 0%nat.
Qed.

End memory_access_tests.
