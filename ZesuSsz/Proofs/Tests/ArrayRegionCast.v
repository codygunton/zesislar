Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Automation2.All.

Lemma array_region_cast_at_base `{!islaG Sigma}
    (base : Z) (bytes : list byte)
    (Hnonnegative : 0 <= base) (Hnowrap : base < word64Modulus) :
  FindHypEqual (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 base)))
    (base ↦ₘ∗ bytes)
    (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 base)) (MKArray 8 base bytes))
    (base ↦ₘ∗ bytes).
Proof. ZesuSsz.Automation2.Hooks.zesu_array_region_selection_if_enabled. Qed.

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
Proof. ZesuSsz.Automation2.Hooks.zesu_array_region_selection_if_enabled. Qed.

Lemma array_region_cast_updated `{!islaG Sigma}
    (base : Z) (before replacement : list byte) (offset : nat)
    (Hnonnegative : 0 <= base) (Hnowrap : base < word64Modulus) :
  let bytes := take offset before ++ replacement ++
    drop (offset + length replacement) before in
  FindHypEqual (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 base)))
    (base ↦ₘ∗ bytes)
    (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 base)) (MKArray 8 base bytes))
    (base ↦ₘ∗ bytes).
Proof. cbn zeta. ZesuSsz.Automation2.Hooks.zesu_array_region_selection_if_enabled. Qed.

Lemma array_region_cast_empty `{!islaG Sigma}
    (base : Z) (Hnonnegative : 0 <= base) (Hnowrap : base < word64Modulus) :
  FindHypEqual (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 base)))
    (base ↦ₘ∗ ([] : list byte))
    (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 base)) (MKArray 8 base []))
    (base ↦ₘ∗ ([] : list byte)).
Proof. ZesuSsz.Automation2.Hooks.zesu_array_region_selection_if_enabled. Qed.

Lemma array_region_cast_reject_wrap `{!islaG Sigma} : True.
Proof.
  Fail assert (Hbad : FindHypEqual (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 (-1))))
    ((-1) ↦ₘ∗ ([] : list byte))
    (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 (-1))) (MKArray 8 (-1) []))
    ((-1) ↦ₘ∗ ([] : list byte)))
    by ZesuSsz.Automation2.Hooks.zesu_array_region_selection_if_enabled.
  exact I.
Qed.

Lemma array_region_cast_finisher_kind `{!islaG Sigma}
    (base : Z) (bytes : list byte)
    (Hnonnegative : 0 <= base) (Hnowrap : base < word64Modulus) : True.
Proof.
  evar (kind : mem_mapsto_kind).
  assert (Hselection : FindHypEqual
    (ZesuMemRegionSearch (bv_unsigned (Z_to_bv 64 base)))
    (base ↦ₘ∗ bytes)
    (mem_mapsto_kind_prop (bv_unsigned (Z_to_bv 64 base)) kind)
    (base ↦ₘ∗ bytes)) by ZesuSsz.Automation2.Finish.zesu_finish.
  assert (Hkind : kind = MKArray 8 base bytes) by reflexivity.
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
Proof. eexists. ZesuSsz.Automation2.Finish.zesu_finish. Qed.
