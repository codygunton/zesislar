Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.MemoryAccess.
Require Import isla.riscv64.riscv64.
From Coq Require Import List Lia.
Local Open Scope Z_scope.

Section Off.
Context `{!islaG Sigma} `{!threadG}.
Lemma memory_region_off : True.
Proof. Fail let _ := constr:(_ : ZesuStepMemoryAccess) in idtac. exact I. Qed.
Lemma memory_region_switch_off (base : Z) (values : list (bv 8)) :
  base ↦ₘ∗ values -∗
  find_in_context (FindMemMapsTo base) (fun _ => True)%I -∗
  find_in_context (FindMemMapsTo base) (fun _ => True)%I.
Proof.
  iIntros "Hvalues Hgoal".
  Fail zesu_memory_access_if_enabled ltac:(idtac).
  Fail let _ := constr:(_ : MemoryAccessSelection base) in idtac.
  iExact "Hgoal".
Qed.
End Off.

Require Import ZesuSsz.Automation.Switches.MemoryAccess.
Section On.
Context `{!islaG Sigma} `{!threadG}.

Definition memory_region_continuation (address : Z) (width : N)
    (kind : mem_mapsto_kind) : iProp Sigma :=
  match kind with
  | MKArray 8 base values =>
      let index := Z.to_nat (address - base) in
        ⌜Z.of_nat index = address - base⌝ ∗
        ⌜(index + N.to_nat width <= length values)%nat⌝ ∗
        (base ↦ₘ∗ values -∗ True)
  | _ => False
  end.

Global Instance : LithiumUnfold (@memory_region_continuation) := I.
Global Typeclasses Opaque memory_region_continuation.

Lemma memory_region_literal (base offset : Z) (values : list (bv 8))
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hextent : offset + 2 <= Z.of_nat (length values))
    (Hnowrap : base + Z.of_nat (length values) <= 2 ^ 64) :
  base ↦ₘ∗ values -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2).
Proof.
  iIntros "Hvalues".
  unfold memory_region_continuation.
  zesu_memory_access_if_enabled ltac:(idtac).
  Fail let _ := constr:(_ : MemoryAccessSelection (base + offset)) in idtac.
  iSplitR.
  - iPureIntro. rewrite Z2Nat.id; lia.
  - iSplitR.
    + iPureIntro. apply Nat2Z.inj_le.
      rewrite Nat2Z.inj_add Z2Nat.id; cbn [N.to_nat]; lia.
    + iIntros "Hvalues". done.
Qed.
Lemma memory_region_one (base offset : Z) (values : list (bv 8))
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hextent : offset + 1 <= Z.of_nat (length values))
    (Hnowrap : base + Z.of_nat (length values) <= 2 ^ 64) :
  base ↦ₘ∗ values -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 1).
Proof.
  iIntros "Hvalues".
  unfold memory_region_continuation.
  zesu_memory_access_if_enabled ltac:(idtac).
  Fail let _ := constr:(_ : MemoryAccessSelection (base + offset)) in idtac.
  iSplitR.
  - iPureIntro. rewrite Z2Nat.id; lia.
  - iSplitR.
    + iPureIntro. apply Nat2Z.inj_le.
      rewrite Nat2Z.inj_add Z2Nat.id; cbn [N.to_nat]; lia.
    + iIntros "Hvalues". done.
Qed.
Lemma memory_region_eight (base offset : Z) (values : list (bv 8))
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hextent : offset + 8 <= Z.of_nat (length values))
    (Hnowrap : base + Z.of_nat (length values) <= 2 ^ 64) :
  base ↦ₘ∗ values -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 8).
Proof.
  iIntros "Hvalues".
  unfold memory_region_continuation.
  zesu_memory_access_if_enabled ltac:(idtac).
  Fail let _ := constr:(_ : MemoryAccessSelection (base + offset)) in idtac.
  iSplitR.
  - iPureIntro. rewrite Z2Nat.id; lia.
  - iSplitR.
    + iPureIntro. apply Nat2Z.inj_le.
      rewrite Nat2Z.inj_add Z2Nat.id; cbn [N.to_nat]; lia.
    + iIntros "Hvalues". done.
Qed.
Lemma memory_region_missing_extent (base offset : Z) (values : list (bv 8))
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hnowrap : base + Z.of_nat (length values) <= 2 ^ 64) :
  base ↦ₘ∗ values -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2) -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2).
Proof.
  iIntros "Hvalues Hgoal".
  unfold memory_region_continuation in *.
  Fail zesu_memory_access_if_enabled ltac:(idtac).
  Fail let _ := constr:(_ : MemoryAccessSelection (base + offset)) in idtac.
  iExact "Hgoal".
Qed.

Lemma memory_region_missing_nowrap (base offset : Z) (values : list (bv 8))
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hextent : offset + 2 <= Z.of_nat (length values)) :
  base ↦ₘ∗ values -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2) -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2).
Proof.
  iIntros "Hvalues Hgoal".
  unfold memory_region_continuation in *.
  Fail zesu_memory_access_if_enabled ltac:(idtac).
  Fail let _ := constr:(_ : MemoryAccessSelection (base + offset)) in idtac.
  iExact "Hgoal".
Qed.

Lemma memory_region_duplicate (base offset : Z) (values other : list (bv 8))
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hextent : offset + 2 <= Z.of_nat (length values))
    (Hnowrap : base + Z.of_nat (length values) <= 2 ^ 64) :
  base ↦ₘ∗ values -∗ base ↦ₘ∗ other -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2) -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2).
Proof.
  iIntros "Hvalues Hother Hgoal".
  unfold memory_region_continuation in *.
  Fail zesu_memory_access_if_enabled ltac:(idtac).
  Fail let _ := constr:(_ : MemoryAccessSelection (base + offset)) in idtac.
  iExact "Hgoal".
Qed.

Lemma memory_region_past_end (base offset : Z) (values : list (bv 8))
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hpast : Z.of_nat (length values) <= offset)
    (Hnowrap : base + Z.of_nat (length values) <= 2 ^ 64) :
  base ↦ₘ∗ values -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2) -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2).
Proof.
  iIntros "Hvalues Hgoal".
  unfold memory_region_continuation in *.
  Fail zesu_memory_access_if_enabled ltac:(idtac).
  Fail let _ := constr:(_ : MemoryAccessSelection (base + offset)) in idtac.
  iExact "Hgoal".
Qed.

Lemma memory_region_wrap (base offset : Z) (values : list (bv 8))
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hextent : offset + 2 <= Z.of_nat (length values)) (Hwrap : 2 ^ 64 < base + Z.of_nat (length values)) :
  base ↦ₘ∗ values -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2) -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2).
Proof.
  iIntros "Hvalues Hgoal".
  unfold memory_region_continuation in *.
  Fail zesu_memory_access_if_enabled ltac:(idtac).
  Fail let _ := constr:(_ : MemoryAccessSelection (base + offset)) in idtac.
  iExact "Hgoal".
Qed.

Lemma memory_region_symbolic (base constant : Z) (index : bv 64) (values : list (bv 8))
    (Hbase : 0 <= base) (Hoffset : 0 <= (bv_unsigned index * 8 + constant))
    (Hextent : (bv_unsigned index * 8 + constant) + 8 <= Z.of_nat (length values))
    (Hnowrap : base + Z.of_nat (length values) <= 2 ^ 64) :
  base ↦ₘ∗ values -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned ((Z_to_bv 64 base + index * Z_to_bv 64 8 + Z_to_bv 64 constant)%bv)))
    (memory_region_continuation (base + (bv_unsigned index * 8 + constant)) 8).
Proof.
  iIntros "Hvalues".
  unfold memory_region_continuation.
  zesu_memory_access_if_enabled ltac:(idtac).
  Fail let _ := constr:(_ : MemoryAccessSelection (base + (bv_unsigned index * 8 + constant))) in idtac.
  iSplitR.
  - iPureIntro. rewrite Z2Nat.id; lia.
  - iSplitR.
    + iPureIntro. apply Nat2Z.inj_le.
      rewrite Nat2Z.inj_add Z2Nat.id; cbn [N.to_nat]; lia.
    + iIntros "Hvalues". done.
Qed.
Lemma memory_region_native_literal (base : Z) (values : list (bv 8))
    (Hbase : 0 <= base)
    (Hextent : 32 + 2 <= Z.of_nat (length values))
    (Hnowrap : base + Z.of_nat (length values) <= 2 ^ 64) :
  base ↦ₘ∗ values -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (32%bv))))
    (memory_region_continuation (base + 32) 2).
Proof.
  iIntros "Hvalues".
  unfold memory_region_continuation.
  zesu_memory_access_if_enabled ltac:(idtac).
  Fail let _ := constr:(_ : MemoryAccessSelection (base + 32)) in idtac.
  iSplitR.
  - iPureIntro. rewrite Z2Nat.id; lia.
  - iSplitR.
    + iPureIntro. apply Nat2Z.inj_le.
      rewrite Nat2Z.inj_add Z2Nat.id; cbn [N.to_nat]; lia.
    + iIntros "Hvalues". done.
Qed.
Lemma memory_region_peer_shelf (base offset : Z) (values : list (bv 8))
    (Hbase : 0 <= base) (Hoffset : 0 <= offset)
    (Hextent : offset + 2 <= Z.of_nat (length values))
    (Hnowrap : base + Z.of_nat (length values) <= 2 ^ 64) :
  base ↦ₘ∗ values -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset))))
    (memory_region_continuation (base + offset) 2).
Proof.
  iIntros "Hvalues".
  unfold memory_region_continuation.
  assert (unrelated : nat) by shelve.
  assert (Hpeer : True).
  2: zesu_memory_access_if_enabled ltac:(idtac).
  2: (iSplitR;
    [iPureIntro; rewrite Z2Nat.id; lia |
     iSplitR;
       [iPureIntro; apply Nat2Z.inj_le;
        rewrite Nat2Z.inj_add Z2Nat.id; cbn [N.to_nat]; lia |
        iIntros "Hvalues"; done]]).
  exact I.
  Unshelve.
  exact 0%nat.
Qed.

End On.
