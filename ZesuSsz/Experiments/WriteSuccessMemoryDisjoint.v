From Coq Require Import Lists.List ZArith.ZArith.
From iris.base_logic.lib Require Import ghost_map.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Experiments.WriteSuccessStackRange.

Import ListNotations.
Open Scope Z_scope.

Lemma mem_mapsto_byte_value_disjoint `{!islaG Sigma}
    (a b : Z) (left right : bv 8) q :
  a ↦ₘ left -∗ b ↦ₘ{q} right -∗ ⌜a <> b⌝.
Proof.
  iIntros "Ha Hb" (->).
  rewrite !mem_mapsto_eq.
  iDestruct "Ha" as (leftLength HleftLength HleftRange) "Ha".
  iDestruct "Hb" as (rightLength HrightLength HrightRange) "Hb".
  have -> : leftLength = 1%nat by nia.
  have -> : rightLength = 1%nat by nia.
  cbn.
  iDestruct "Ha" as "[Ha _]".
  iDestruct "Hb" as "[Hb _]".
  rewrite !mem_mapsto_byte_eq.
  iDestruct "Ha" as (leftAddress HleftAddress) "Ha".
  iDestruct "Hb" as (rightAddress HrightAddress) "Hb".
  rewrite HleftAddress in HrightAddress.
  simplify_eq.
  iDestruct (ghost_map_elem_ne with "Ha Hb") as %Hdifferent.
  done.
Qed.

Lemma writeSuccessScratch_uninit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) :
  writeSuccessScratch sp -∗ (bv_unsigned sp - 104) ↦ₘ? 104.
Proof.
  rewrite /writeSuccessScratch.
  iIntros "Hscratch".
  iDestruct "Hscratch" as
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12)
    "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 &
      H10 & H11 & H12 & _)".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H0") as "H0".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H1") as "H1".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H2") as "H2".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H3") as "H3".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H4") as "H4".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H5") as "H5".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H6") as "H6".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H7") as "H7".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H8") as "H8".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H9") as "H9".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H10") as "H10".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H11") as "H11".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H12") as "H12".
  iAssert ((bv_unsigned sp - 104) ↦ₘ? 16)%I
    with "[H0 H1]" as "H01".
  { iApply (mem_mapsto_uninit_combine 8 with "H0"); first lia.
    have -> : bv_unsigned sp - 104 + 8 = bv_unsigned sp - 96 by lia.
    iExact "H1". }
  iAssert ((bv_unsigned sp - 104) ↦ₘ? 24)%I
    with "[H01 H2]" as "H02".
  { iApply (mem_mapsto_uninit_combine 16 with "H01"); first lia.
    have -> : bv_unsigned sp - 104 + 16 = bv_unsigned sp - 88 by lia.
    iExact "H2". }
  iAssert ((bv_unsigned sp - 104) ↦ₘ? 32)%I
    with "[H02 H3]" as "H03".
  { iApply (mem_mapsto_uninit_combine 24 with "H02"); first lia.
    have -> : bv_unsigned sp - 104 + 24 = bv_unsigned sp - 80 by lia.
    iExact "H3". }
  iAssert ((bv_unsigned sp - 104) ↦ₘ? 40)%I
    with "[H03 H4]" as "H04".
  { iApply (mem_mapsto_uninit_combine 32 with "H03"); first lia.
    have -> : bv_unsigned sp - 104 + 32 = bv_unsigned sp - 72 by lia.
    iExact "H4". }
  iAssert ((bv_unsigned sp - 104) ↦ₘ? 48)%I
    with "[H04 H5]" as "H05".
  { iApply (mem_mapsto_uninit_combine 40 with "H04"); first lia.
    have -> : bv_unsigned sp - 104 + 40 = bv_unsigned sp - 64 by lia.
    iExact "H5". }
  iAssert ((bv_unsigned sp - 104) ↦ₘ? 56)%I
    with "[H05 H6]" as "H06".
  { iApply (mem_mapsto_uninit_combine 48 with "H05"); first lia.
    have -> : bv_unsigned sp - 104 + 48 = bv_unsigned sp - 56 by lia.
    iExact "H6". }
  iAssert ((bv_unsigned sp - 104) ↦ₘ? 64)%I
    with "[H06 H7]" as "H07".
  { iApply (mem_mapsto_uninit_combine 56 with "H06"); first lia.
    have -> : bv_unsigned sp - 104 + 56 = bv_unsigned sp - 48 by lia.
    iExact "H7". }
  iAssert ((bv_unsigned sp - 104) ↦ₘ? 72)%I
    with "[H07 H8]" as "H08".
  { iApply (mem_mapsto_uninit_combine 64 with "H07"); first lia.
    have -> : bv_unsigned sp - 104 + 64 = bv_unsigned sp - 40 by lia.
    iExact "H8". }
  iAssert ((bv_unsigned sp - 104) ↦ₘ? 80)%I
    with "[H08 H9]" as "H09".
  { iApply (mem_mapsto_uninit_combine 72 with "H08"); first lia.
    have -> : bv_unsigned sp - 104 + 72 = bv_unsigned sp - 32 by lia.
    iExact "H9". }
  iAssert ((bv_unsigned sp - 104) ↦ₘ? 88)%I
    with "[H09 H10]" as "H010".
  { iApply (mem_mapsto_uninit_combine 80 with "H09"); first lia.
    have -> : bv_unsigned sp - 104 + 80 = bv_unsigned sp - 24 by lia.
    iExact "H10". }
  iAssert ((bv_unsigned sp - 104) ↦ₘ? 96)%I
    with "[H010 H11]" as "H011".
  { iApply (mem_mapsto_uninit_combine 88 with "H010"); first lia.
    have -> : bv_unsigned sp - 104 + 88 = bv_unsigned sp - 16 by lia.
    iExact "H11". }
  iApply (mem_mapsto_uninit_combine 96 with "H011"); first lia.
  have -> : bv_unsigned sp - 104 + 96 = bv_unsigned sp - 8 by lia.
  iExact "H12".
Qed.

Lemma writeSuccessStackTiles_uninit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) :
  (bv_unsigned sp - 2080) ↦ₘ? 32 -∗
  (bv_unsigned sp - 2048) ↦ₘ? 48 -∗
  (bv_unsigned sp - 2000) ↦ₘ? 1896 -∗
  writeSuccessScratch sp -∗
  (bv_unsigned sp - 2080) ↦ₘ? 2080.
Proof.
  iIntros "H32 H48 H1896 Hscratch".
  iPoseProof (writeSuccessScratch_uninit with "Hscratch") as "H104".
  iAssert ((bv_unsigned sp - 2080) ↦ₘ? 80)%I
    with "[H32 H48]" as "H80".
  { iApply (mem_mapsto_uninit_combine 32 with "H32"); first lia.
    have -> : bv_unsigned sp - 2080 + 32 = bv_unsigned sp - 2048 by lia.
    iExact "H48". }
  iAssert ((bv_unsigned sp - 2080) ↦ₘ? 1976)%I
    with "[H80 H1896]" as "H1976".
  { iApply (mem_mapsto_uninit_combine 80 with "H80"); first lia.
    have -> : bv_unsigned sp - 2080 + 80 = bv_unsigned sp - 2000 by lia.
    iExact "H1896". }
  iApply (mem_mapsto_uninit_combine 1976 with "H1976"); first lia.
  have -> : bv_unsigned sp - 2080 + 1976 = bv_unsigned sp - 104 by lia.
  iExact "H104".
Qed.

Lemma mem_mapsto_uninit_disjoint `{!islaG Sigma}
    (a b : Z) (n : N) q (bytes : list (bv 8)) :
  (0 < n)%N ->
  (a ↦ₘ? Z.of_N n ∗ b ↦ₘ{q}∗ bytes ⊢
    ⌜writeSuccessAvoidsRange a (a + Z.of_N n) b (length bytes)⌝)%I.
Proof.
  intros Hn.
  iIntros "[Huninit Hbytes]".
  iDestruct (mem_mapsto_uninit_to_byte_array with "Huninit") as
    (uninitBytes HuninitLength) "Huninit".
  destruct (decide (writeSuccessAvoidsRange
    a (a + Z.of_N n) b (length bytes))) as [Havoids | Hoverlap].
  { done. }
  iExFalso.
  unfold writeSuccessAvoidsRange in Hoverlap.
  have HnZ : (0 < Z.of_N n)%Z by lia.
  have HbytesLength : (0 < length bytes)%nat by lia.
  have HoverlapLeft : (a < b + Z.of_nat (length bytes))%Z by lia.
  have HoverlapRight : (b < a + Z.of_N n)%Z by lia.
  set (address := Z.max a b).
  set (leftIndex := Z.to_nat (address - a)).
  set (rightIndex := Z.to_nat (address - b)).
  have HleftIndex : (leftIndex < length uninitBytes)%nat.
  { subst leftIndex address. apply Nat2Z.inj_lt.
    rewrite Z2Nat.id; [rewrite HuninitLength | lia]. lia. }
  have HrightIndex : (rightIndex < length bytes)%nat.
  { subst rightIndex address. apply Nat2Z.inj_lt.
    rewrite Z2Nat.id; lia. }
  have [leftByte HleftByte] :=
    lookup_lt_is_Some_2 uninitBytes leftIndex HleftIndex.
  have [rightByte HrightByte] :=
    lookup_lt_is_Some_2 bytes rightIndex HrightIndex.
  iDestruct (mem_mapsto_array_lookup_acc 8%N a leftIndex uninitBytes
    (DfracOwn 1) 1%N leftByte with "Huninit") as "[Hleft _]";
    [done | exact HleftByte |].
  iDestruct (mem_mapsto_array_lookup_acc 8%N b rightIndex bytes q 1%N
    rightByte with "Hbytes") as "[Hright _]";
    [done | exact HrightByte |].
  have HaddressLeft :
      (a + Z.of_nat leftIndex * Z.of_N 1 = address)%Z.
  { subst leftIndex address. rewrite Z2Nat.id; lia. }
  have HaddressRight :
      (b + Z.of_nat rightIndex * Z.of_N 1 = address)%Z.
  { subst rightIndex address. rewrite Z2Nat.id; lia. }
  iEval (rewrite HaddressLeft) in "Hleft".
  iEval (rewrite HaddressRight) in "Hright".
  iDestruct (mem_mapsto_byte_value_disjoint with "Hleft Hright") as %Hne.
  done.
Qed.

Print Assumptions mem_mapsto_byte_value_disjoint.
Print Assumptions mem_mapsto_uninit_disjoint.
Print Assumptions writeSuccessScratch_uninit.
Print Assumptions writeSuccessStackTiles_uninit.
