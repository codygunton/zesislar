Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import List.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.

Lemma array_region_search_opt_in : True.
Proof.
  Fail let enabled := constr:(_ : ZesuStepArrayRegionBounds) in idtac.
  exact I.
Qed.

Lemma array_region_search_legacy_base (p : Z) (bytes : list (bv 8)) : True.
Proof.
  evar (index : nat).
  assert (Hbase :
    (p <= p + 0 < p + Z.of_nat (length
      (take index bytes ++ [0%bv; 0%bv] ++ drop (index + 2) bytes)))%Z \/
    p = (p + 0)%Z) by zesu_region_bounds.
  let value := eval unfold index in index in unify value 0%nat.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.ArrayRegionBounds.

Lemma array_region_search_unresolved_on (p : Z) (bytes : list (bv 8)) : True.
Proof.
  evar (index : nat).
  assert (Hbase :
    (p <= p + 0 < p + Z.of_nat (length
      (take index bytes ++ [0%bv; 0%bv] ++ drop (index + 2) bytes)))%Z \/
    p = (p + 0)%Z) by zesu_region_bounds.
  let value := eval unfold index in index in unify value 0%nat.
  exact I.
Qed.

Lemma array_region_search_base_selector `{!islaG Sigma}
    (p : Z) (bytes : list (bv 8)) (index : nat) :
  FindHypEqual (ZesuMemRegionSearch (p + 0))
    (p ↦ₘ∗ (take index bytes ++ [0%bv; 0%bv] ++ drop (index + 2) bytes))
    (mem_mapsto_kind_prop (p + 0)
      (MKArray 8 p (take index bytes ++ [0%bv; 0%bv] ++ drop (index + 2) bytes)))
    (p ↦ₘ∗ (take index bytes ++ [0%bv; 0%bv] ++ drop (index + 2) bytes)).
Proof. typeclasses eauto. Qed.

Lemma array_region_search_reject_wrong_base (p : Z) (bytes : list (bv 8)) : True.
Proof.
  Fail assert (Hwrong :
    (p <= p + 1 < p + Z.of_nat (length bytes))%Z \/ p = (p + 1)%Z)
    by zesu_region_bounds.
  exact I.
Qed.

Lemma array_region_search_69e8 `{!islaG Sigma} (args : DecodeItemArgs) :
  exists kind : mem_mapsto_kind,
    FindHypEqual (ZesuMemRegionSearch (decodeItemOutputPointer args + 0))
      (decodeItemOutputPointer args ↦ₘ∗
        (take 32 (decodeItemBeforeStorage args) ++
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16)) (Z.ones 8)) ::
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16) ≫ 8) (Z.ones 8)) ::
         drop 34 (decodeItemBeforeStorage args)))
      (mem_mapsto_kind_prop (decodeItemOutputPointer args + 0) kind)
      (decodeItemOutputPointer args ↦ₘ∗
        (take 32 (decodeItemBeforeStorage args) ++
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16)) (Z.ones 8)) ::
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16) ≫ 8) (Z.ones 8)) ::
         drop 34 (decodeItemBeforeStorage args))).
Proof. eexists. zesu_finish_selectors. Qed.

Lemma array_region_search_69b0 `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
    (Hlower : 0 <= decodeItemOutputPointer args)
    (Hupper : decodeItemOutputPointer args + 40 < 2 ^ 64) :
  exists kind : mem_mapsto_kind,
    FindHypEqual (ZesuMemRegionSearch
      (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args))))
      (decodeItemOutputPointer args ↦ₘ∗
        (take 32 (returnStorage locals) ++
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16)) (Z.ones 8)) ::
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16) ≫ 8) (Z.ones 8)) ::
         drop 34 (returnStorage locals)))
      (mem_mapsto_kind_prop
        (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args))) kind)
      (decodeItemOutputPointer args ↦ₘ∗
        (take 32 (returnStorage locals) ++
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16)) (Z.ones 8)) ::
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16) ≫ 8) (Z.ones 8)) ::
         drop 34 (returnStorage locals))).
Proof. eexists. zesu_finish_selectors. Qed.

Lemma array_region_search_6a78 `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
    (Hlower : 0 <= decodeItemOutputPointer args)
    (Hupper : decodeItemOutputPointer args + 40 < 2 ^ 64) :
  exists kind : mem_mapsto_kind,
    FindHypEqual (ZesuMemRegionSearch
      (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args))))
      (decodeItemOutputPointer args ↦ₘ∗
        (take 32 (returnStorage locals) ++
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16)) (Z.ones 8)) ::
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16) ≫ 8) (Z.ones 8)) ::
         drop 34 (returnStorage locals)))
      (mem_mapsto_kind_prop
        (bv_unsigned (Z_to_bv 64 (decodeItemOutputPointer args))) kind)
      (decodeItemOutputPointer args ↦ₘ∗
        (take 32 (returnStorage locals) ++
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16)) (Z.ones 8)) ::
         Z_to_bv 8 (Z.land (bv_unsigned (0 : bv 16) ≫ 8) (Z.ones 8)) ::
         drop 34 (returnStorage locals))).
Proof. eexists. zesu_finish_selectors. Qed.
