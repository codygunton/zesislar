Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SwitchDispatch.
Set Default Proof Mode "Classic".
Require Import ZesuSsz.Automation.Switches.RegionFaultCastHypotheses.
Open Scope Z_scope.

Lemma region_cast_nonzero (count : Z) (Hnonnegative : 0 <= count)
    (Hnonzero : bv_unsigned (Z_to_bv 64 count) <> 0) : 0 < count.
Proof.
  zesu_region_fault_cast_hypotheses_if_enabled. bv_solve.
Qed.

Lemma region_cast_multiple (left right : Z)
    (Hleft : bv_unsigned (Z_to_bv 64 left) <> 0)
    (Hright : bv_unsigned (Z_to_bv 32 right) <> 0)
    (HleftNonnegative : 0 <= left) (HrightNonnegative : 0 <= right) :
    0 < left + right.
Proof.
  zesu_region_fault_cast_hypotheses_if_enabled. bv_solve.
Qed.

Lemma region_cast_symbolic_local (count : Z) (Hnonnegative : 0 <= count) :
    let local_count := count in
    bv_unsigned (Z_to_bv 64 local_count) <> 0 -> 0 < local_count.
Proof.
  intros local_count Hnonzero.
  zesu_region_fault_cast_hypotheses_if_enabled. bv_solve.
Qed.

Lemma region_cast_cached_off (count : Z) (Hnonnegative : 0 <= count)
    (Hnonzero : bv_unsigned (Z_to_bv 64 count) <> 0) : 0 < count.
Proof.
  assert (Hcache : ZesuSwitchDispatchCache
    [(ZesuStepRegionFaultCastHypotheses, false)]) by constructor.
  first [zesu_region_fault_cast_hypotheses_if_enabled;
    fail 1 "unexpected normalization success" | idtac].
  rewrite Z_to_bv_unsigned in Hnonzero. bv_solve.
Qed.

Lemma region_cast_nonmatching (value : bv 64)
    (Hnonzero : bv_unsigned value <> 0) : 0 < bv_unsigned value.
Proof.
  first [zesu_region_fault_cast_hypotheses_if_enabled;
    fail 1 "unexpected normalization success" | idtac].
  bv_solve.
Qed.

Lemma region_cast_rollback (count : Z) (Hnonnegative : 0 <= count)
    (Hnonzero : bv_unsigned (Z_to_bv 64 count) <> 0) : 0 < count.
Proof.
  assert_fails (zesu_region_fault_cast_hypotheses_if_enabled; fail 0).
  let statement := type of Hnonzero in
  constr_eq statement (bv_unsigned (Z_to_bv 64 count) <> 0).
  zesu_region_fault_cast_hypotheses_if_enabled. bv_solve.
Qed.

Lemma region_cast_shared_evar_rejected : True.
Proof.
  evar (pending : Z).
  assert (Hopen : bv_unsigned (Z_to_bv 64 pending) =
    bv_unsigned (Z_to_bv 64 pending)) by reflexivity.
  assert (Hprobe : 0 <= bv_unsigned (Z_to_bv 64 pending)).
  1: (first [zesu_region_fault_cast_hypotheses_if_enabled;
    fail 1 "unexpected normalization success" | idtac]).
  1: (let value := eval unfold pending in pending in
    has_evar value; unify value 0%Z; bv_solve).
  exact I.
Qed.

Lemma region_cast_unrelated_shared_evar (count : Z)
    (Hnonnegative : 0 <= count)
    (Hnonzero : bv_unsigned (Z_to_bv 64 count) <> 0) : True.
Proof.
  evar (pending : nat).
  assert (Haux : Coq.Init.Logic.True) by shelve.
  assert (Hprobe : 0 < count).
  1: zesu_region_fault_cast_hypotheses_if_enabled.
  1: (let value := eval unfold pending in pending in has_evar value; bv_solve).
  1: (let value := eval unfold pending in pending in
    has_evar value; unify value 0%nat; exact I).
  Unshelve. all: exact I.
Qed.

Lemma region_cast_nested_evar_rejected : True.
Proof.
  evar (pending : Z).
  pose (first_alias := pending).
  pose (second_alias := first_alias).
  assert (Hopen : bv_unsigned (Z_to_bv 64 second_alias) =
    bv_unsigned (Z_to_bv 64 second_alias)) by reflexivity.
  assert (Hprobe : 0 <= bv_unsigned (Z_to_bv 64 second_alias)).
  1: (first [zesu_region_fault_cast_hypotheses_if_enabled;
    fail 1 "unexpected normalization success" | idtac]).
  1: (let value := eval unfold pending in pending in
    has_evar value; unify value 0%Z; bv_solve).
  exact I.
Qed.
