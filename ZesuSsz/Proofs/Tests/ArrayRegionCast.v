Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.

Lemma array_region_cast_opt_in : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepArrayRegionBounds) in idtac.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.ArrayRegionBounds.

Lemma array_region_cast_at_base `{!islaG Sigma}
    (base : Z) (bytes : list byte)
    (Hnonnegative : 0 <= base) (Hnowrap : base < word64Modulus) :
  FindHypEqual (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 base)))
    (base ↦ₘ∗ bytes)
    (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 base)) (MKArray 8 base bytes))
    (base ↦ₘ∗ bytes).
Proof. zesu_array_region_selection_if_enabled. Qed.

Lemma array_region_cast_projection `{!islaG Sigma}
    (args : DecodeItemArgs) (bytes : list byte)
    (Hnonnegative : 0 <= decodeItemOutputPointer args)
    (Hnowrap : decodeItemOutputPointer args + 40 < word64Modulus) :
  FindHypEqual
    (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args))))
    (decodeItemOutputPointer args ↦ₘ∗ bytes)
    (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args)))
      (MKArray 8 (decodeItemOutputPointer args) bytes))
    (decodeItemOutputPointer args ↦ₘ∗ bytes).
Proof. zesu_array_region_selection_if_enabled. Qed.

Lemma array_region_cast_updated `{!islaG Sigma}
    (base : Z) (before replacement : list byte) (offset : nat)
    (Hnonnegative : 0 <= base) (Hnowrap : base < word64Modulus) :
  let bytes := take offset before ++ replacement ++
    drop (offset + length replacement) before in
  FindHypEqual (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 base)))
    (base ↦ₘ∗ bytes)
    (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 base)) (MKArray 8 base bytes))
    (base ↦ₘ∗ bytes).
Proof. cbn zeta. zesu_array_region_selection_if_enabled. Qed.

Lemma array_region_cast_empty `{!islaG Sigma}
    (base : Z) (Hnonnegative : 0 <= base) (Hnowrap : base < word64Modulus) :
  FindHypEqual (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 base)))
    (base ↦ₘ∗ ([] : list byte))
    (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 base)) (MKArray 8 base []))
    (base ↦ₘ∗ ([] : list byte)).
Proof. zesu_array_region_selection_if_enabled. Qed.

Lemma array_region_cast_reject_wrap `{!islaG Sigma} : True.
Proof.
  Fail assert (Hbad : FindHypEqual (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 (-1))))
    ((-1) ↦ₘ∗ ([] : list byte))
    (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 (-1))) (MKArray 8 (-1) []))
    ((-1) ↦ₘ∗ ([] : list byte))) by zesu_array_region_selection_if_enabled.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.EvarSideconditionGuard.

Lemma array_region_cast_finisher_kind `{!islaG Sigma}
    (base : Z) (bytes : list byte)
    (Hnonnegative : 0 <= base) (Hnowrap : base < word64Modulus) : True.
Proof.
  evar (kind : mem_mapsto_kind).
  assert (Hselection : FindHypEqual
    (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 base)))
    (base ↦ₘ∗ bytes)
    (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 base)) kind)
    (base ↦ₘ∗ bytes)) by zesu_finish.
  assert (Hkind : kind = MKArray 8 base bytes) by reflexivity.
  exact I.
Qed.

Lemma array_region_cast_preserves_deferral : True.
Proof.
  evar (witness : nat).
  assert (Hdeferred : witness = 0%nat).
  { Fail progress zesu_finish. unfold witness. reflexivity. }
  exact I.
Qed.

Lemma array_region_cast_finisher_direct_kind `{!islaG Sigma}
    (base : Z) (bytes : list byte)
    (Hnonnegative : 0 <= base) (Hnowrap : base < word64Modulus) :
  exists kind : mem_mapsto_kind,
    FindHypEqual (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 base)))
      (base ↦ₘ∗ bytes)
      (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 base)) kind)
      (base ↦ₘ∗ bytes).
Proof. eexists. zesu_finish. Qed.
