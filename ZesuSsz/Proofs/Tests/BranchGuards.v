Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import isla.riscv64.riscv64.
Open Scope Z_scope.

Lemma branch_guards_disabled (word : bv 64) : True.
Proof.
  Fail let marker := constr:(_ : ZesuStepBranchGuards) in idtac.
  Fail assert (SimplImpl (bv_signed (bv_zero_extend 128 word) < 0)
    (bv_unsigned word < 0)) by zesu_branch_guard_simpl_impl.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.BranchGuards.

Lemma branch_guard_plain_mask_control (value : bv 64) :
  129 <= bv_unsigned value <= 183 ->
  SimplImpl (bv_signed (bv_zero_extend 128 (bv_and value 127)) < 42)
    (bv_unsigned value - 128 < 42).
Proof. intro Hrange. zesu_branch_guard_simpl_impl. Qed.
Lemma branch_guard_add_mask_control (value : bv 64) :
  192 <= bv_unsigned value <= 247 ->
  SimplImpl (bv_signed (bv_zero_extend 128 (bv_and (value + 64) 255)) < 42)
    (bv_unsigned value - 192 < 42).
Proof. intro Hrange. zesu_branch_guard_simpl_impl. Qed.
Lemma branch_guard_signed_mask_control (value : bv 8) :
  SimplImpl (bv_unsigned (bv_and (Z_to_bv 64 (bv_signed value)) 255) = 128)
    (bv_unsigned value = 128).
Proof. zesu_branch_guard_simpl_impl. Qed.
Lemma branch_guard_sign_control (value : bv 8) :
  SimplImpl (bv_signed value < 0) (128 <= bv_unsigned value).
Proof. zesu_branch_guard_simpl_impl. Qed.
Lemma branch_guard_alias_mask_control (value : bv 64) :
  129 <= bv_unsigned value <= 183 ->
  let masked := bv_and value 127 in
  SimplImpl (bv_signed (bv_zero_extend 128 masked) < 42)
    (bv_unsigned value - 128 < 42).
Proof. intros Hrange masked. zesu_branch_guard_simpl_impl. Qed.

(* Trace-shape controls use arbitrary words. They name no contract predicate. *)
Lemma branch_guard_parent_unsigned_lt (left right : bv 64) :
  SimplImpl (bv_signed (bv_zero_extend 128 left) < bv_signed (bv_zero_extend 128 right))
    (bv_unsigned left < bv_unsigned right).
Proof. zesu_branch_guard_simpl_impl. Qed.
Lemma branch_guard_next_negated_unsigned_ge (left right : bv 64) :
  SimplImpl (~ bv_signed (bv_zero_extend 128 left) >= bv_signed (bv_zero_extend 128 right))
    (~ bv_unsigned left >= bv_unsigned right).
Proof. zesu_branch_guard_simpl_impl. Qed.
Lemma branch_guard_free_unsigned_ge (left right : bv 64) :
  SimplImpl (bv_signed (bv_zero_extend 128 left) >= bv_signed (bv_zero_extend 128 right))
    (bv_unsigned left >= bv_unsigned right).
Proof. zesu_branch_guard_simpl_impl. Qed.
Lemma branch_guard_parent_status_low_mask (word : bv 64) :
  2 <= bv_unsigned word < 4 ->
  SimplImpl (bv_unsigned (bv_and word 1) = 0) (bv_unsigned word - 2 = 0).
Proof. intro Hrange. zesu_branch_guard_simpl_impl. Qed.
Lemma branch_guard_free_low_mask (word : bv 64) :
  64 <= bv_unsigned word < 128 ->
  SimplImpl (bv_unsigned (bv_and word 63) = 0) (bv_unsigned word - 64 = 0).
Proof. intro Hrange. zesu_branch_guard_simpl_impl. Qed.
Lemma branch_guard_signed_mask_bv_control (word : bv 8) :
  SimplImpl (bv_and (Z_to_bv 64 (bv_signed word)) 255 = (128%bv : bv 64))
    (bv_unsigned word = 128).
Proof. zesu_branch_guard_simpl_impl. Qed.
Lemma branch_guard_extended_sign_control (word : bv 8) :
  SimplImpl (~ bv_signed (bv_sign_extend 128 (bv_sign_extend 64 word)) < bv_signed (0%bv : bv 128))
    (~ 128 <= bv_unsigned word).
Proof. zesu_branch_guard_simpl_impl. Qed.
Lemma branch_guard_plain_equality_preserved (left right : bv 64) :
  SimplImpl (left = right) (left = right).
Proof. Fail zesu_branch_guard_simpl_impl. unfold SimplImpl; tauto. Qed.
Lemma branch_guard_negated_equality_preserved (left right : bv 64) :
  SimplImpl (left <> right) (left <> right).
Proof. Fail zesu_branch_guard_simpl_impl. unfold SimplImpl; tauto. Qed.
Remove Hints zesu_branch_guards_enabled : typeclass_instances.
Lemma branch_guard_disabled_refusal (word : bv 64) : True.
Proof.
  Fail assert (SimplImpl (bv_signed (bv_zero_extend 128 word) < 0)
    (bv_unsigned word < 0)) by zesu_branch_guard_simpl_impl.
  exact I.
Qed.
#[local] Existing Instance zesu_branch_guards_enabled.
Lemma branch_guard_output_inference_control (value : bv 64) :
  129 <= bv_unsigned value <= 183 -> True.
Proof.
  intro Hrange. evar (normalized : Prop).
  assert (SimplImpl (bv_unsigned (bv_and value 127) < 42) normalized)
    by zesu_branch_guard_simpl_impl.
  change (SimplImpl (bv_unsigned (bv_and value 127) < 42)
    (bv_unsigned value - 128 < 42)) in H.
  exact I.
Qed.
Lemma branch_guard_symbolic_mask_refusal (value mask : bv 64) : True.
Proof.
  evar (normalized : Prop).
  let hole := eval unfold normalized in normalized in is_evar hole.
  Fail assert (SimplImpl (bv_unsigned (bv_and value mask) = 0) normalized)
    by zesu_branch_guard_simpl_impl.
  let hole := eval unfold normalized in normalized in is_evar hole.
  let body := eval unfold normalized in normalized in
  let proposition := constr:(True) in unify body proposition.
  exact I.
Qed.
Lemma branch_guard_nonmask_refusal (value : bv 64) : True.
Proof.
  evar (normalized : Prop).
  let hole := eval unfold normalized in normalized in is_evar hole.
  Fail assert (SimplImpl (bv_unsigned (bv_and value 5) = 0) normalized)
    by zesu_branch_guard_simpl_impl.
  let hole := eval unfold normalized in normalized in is_evar hole.
  let body := eval unfold normalized in normalized in
  let proposition := constr:(True) in unify body proposition.
  exact I.
Qed.
Lemma branch_guard_missing_range_refusal (value : bv 64) : True.
Proof.
  evar (normalized : Prop).
  let hole := eval unfold normalized in normalized in is_evar hole.
  Fail assert (SimplImpl (bv_unsigned (bv_and value 127) = 0) normalized)
    by zesu_branch_guard_simpl_impl.
  let hole := eval unfold normalized in normalized in is_evar hole.
  let body := eval unfold normalized in normalized in
  let proposition := constr:(True) in unify body proposition.
  exact I.
Qed.
Lemma branch_guard_evar_refusal (value : bv 64) : True.
Proof.
  evar (unknown : bv 64).
  let hole := eval unfold unknown in unknown in is_evar hole.
  evar (normalized : Prop).
  let hole := eval unfold normalized in normalized in is_evar hole.
  Fail assert (SimplImpl (bv_unsigned (bv_and unknown 127) = 0) normalized)
    by zesu_branch_guard_simpl_impl.
  let hole := eval unfold normalized in normalized in is_evar hole.
  let body := eval unfold normalized in normalized in
  let proposition := constr:(True) in unify body proposition.
  let hole := eval unfold unknown in unknown in is_evar hole.
  let body := eval unfold unknown in unknown in
  let zero := constr:(Z_to_bv 64 0) in unify body zero.
  exact I.
Qed.
Print Assumptions branch_guard_plain_mask_control.
Print Assumptions branch_guard_add_mask_control.
Print Assumptions branch_guard_signed_mask_control.
Print Assumptions branch_guard_sign_control.

Print Assumptions branch_guard_parent_unsigned_lt.
Print Assumptions branch_guard_next_negated_unsigned_ge.
Print Assumptions branch_guard_free_unsigned_ge.
Print Assumptions branch_guard_parent_status_low_mask.
Print Assumptions branch_guard_free_low_mask.
Print Assumptions branch_guard_signed_mask_bv_control.
Print Assumptions branch_guard_extended_sign_control.
Print Assumptions branch_guard_plain_equality_preserved.
Print Assumptions branch_guard_negated_equality_preserved.
Print Assumptions branch_guard_disabled_refusal.

Print Assumptions branch_guard_output_inference_control.

Lemma branch_guard_normalizer_enabled (word : bv 64) :
  (bv_signed (bv_zero_extend 128 word) < 0) = (bv_unsigned word < 0).
Proof. zesu_branch_guard_normalize_hook. Qed.
Lemma branch_guard_cached_off_refusal (word : bv 64) :
  129 <= bv_unsigned word <= 183 -> True.
Proof.
  intro Hrange.
  assert (Hcache : ZesuSsz.Automation.SwitchDispatch.ZesuSwitchDispatchCache
    [(ZesuStepBranchGuards, false)]) by constructor.
  Fail assert (SimplImpl (bv_signed (bv_zero_extend 128 word) < 0)
    (bv_unsigned word < 0)) by zesu_branch_guard_simpl_impl.
  Fail assert ((bv_signed (bv_zero_extend 128 word) < 0) = (bv_unsigned word < 0))
    by zesu_branch_guard_normalize_hook.
  Fail assert (bv_unsigned (bv_and word 127) = bv_unsigned word - 128)
    by zesu_branch_guard_solve_if_enabled.
  exact I.
Qed.
Remove Hints zesu_branch_guards_enabled : typeclass_instances.
Lemma branch_guard_cached_on_without_instance (word : bv 64) :
  129 <= bv_unsigned word <= 183 ->
  bv_unsigned (bv_and word 127) = bv_unsigned word - 128.
Proof.
  intro Hrange.
  assert (Hcache : ZesuSsz.Automation.SwitchDispatch.ZesuSwitchDispatchCache
    [(ZesuStepBranchGuards, true)]) by constructor.
  zesu_branch_guard_solve_if_enabled.
Qed.
Print Assumptions branch_guard_normalizer_enabled.
Print Assumptions branch_guard_cached_off_refusal.
Print Assumptions branch_guard_cached_on_without_instance.
