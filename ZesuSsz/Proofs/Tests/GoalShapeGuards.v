Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.

Set Default Proof Using "Type".

(* Each goal-shape guard of GoalShape.v: one goal on which the guarded
   alternative may run, one on which it is skipped. *)

Ltac class_is c := let k := zesu_goal_class in constr_eq k c.
Ltac class_is_not c := let k := zesu_goal_class in assert_fails (constr_eq k c).

Section guards.
Context `{!islaG Sigma} `{!threadG}.
Context (P : iProp Sigma).

(* Memory finder: register cursor, stack write, integer array address, cell chain. *)
Lemma class_find_mem : ⊢ find_in_context (FindMemMapsTo 8) (fun _ => True : iProp Sigma)%I.
Proof. iStartProof. class_is ZGfind_mem. class_is_not ZGfind_reg. Abort.

(* Register finder: region fault, saved-register package. *)
Lemma class_find_reg : ⊢ find_in_context (FindRegMapsTo "x9") (fun _ => True : iProp Sigma)%I.
Proof. iStartProof. class_is ZGfind_reg. class_is_not ZGfind_mem. Abort.

(* Structured-register finder: system-register package. *)
Lemma class_find_sreg :
  ⊢ find_in_context (FindStructRegMapsTo "mstatus" "bits") (fun _ => True : iProp Sigma)%I.
Proof. iStartProof. class_is ZGfind_sreg. class_is_not ZGfind_reg. Abort.

(* Instruction finder: instruction bundle. *)
Lemma class_find_instr : ⊢ find_in_context (FindInstrKind 8 true) (fun _ => True : iProp Sigma)%I.
Proof. iStartProof. class_is ZGfind_instr. class_is_not ZGfind_mem. Abort.

(* Conjunction: register cursor, region fault. *)
Lemma class_and : ⊢ (P ∧ P)%I.
Proof. iStartProof. class_is ZGand. class_is_not ZGsep. Abort.

(* Coq goal: region fault; a product is not one. *)
Lemma class_prop : True.
Proof. class_is ZGprop. class_is_not ZGprod. exact I. Qed.
Lemma class_prod : forall n : nat, n = n.
Proof. class_is ZGprod. class_is_not ZGprop. reflexivity. Qed.

(* Universal: codec read consumer. *)
Lemma class_all : ⊢ (∀ x : bv 64, ⌜x = x⌝ -∗ P)%I.
Proof. iStartProof. class_is ZGall. class_is_not ZGwand. Abort.

(* Named entry, existential, pure, separating conjunctions: union witness
   step; the conjunctions also open matching resources and two-level frames,
   pure targets also extract descriptors. *)
Lemma class_name : ⊢ P.
Proof. iStartProof. class_is ZGname. class_is_not ZGpure. Abort.
Lemma class_ex : ⊢ (∃ x : Z, ⌜x = 0⌝ : iProp Sigma)%I.
Proof. iStartProof. class_is ZGex. class_is_not ZGall. Abort.
Lemma class_pure : ⊢ (⌜True⌝ : iProp Sigma)%I.
Proof. iStartProof. class_is ZGpure. class_is_not ZGsep_pure. Abort.
Lemma class_sep_pure : ⊢ (⌜True⌝ ∗ P)%I.
Proof. iStartProof. class_is ZGsep_pure. class_is_not ZGsep. Abort.
Lemma class_sep_ex : ⊢ ((∃ x : Z, ⌜x = 0⌝) ∗ P)%I.
Proof. iStartProof. class_is ZGsep_ex. class_is_not ZGsep_pure. Abort.
Lemma class_sep : ⊢ (P ∗ P)%I.
Proof. iStartProof. class_is ZGsep. class_is_not ZGsep_ex. Abort.
Lemma class_wand : ⊢ (P -∗ P)%I.
Proof. iStartProof. class_is ZGwand. class_is_not ZGname. Abort.

(* Subsumption: packed-word normalisation. *)
Lemma class_subsume : ⊢ subsume P (fun _ : unit => P) (fun _ => True : iProp Sigma)%I.
Proof. iStartProof. class_is ZGsubsume. class_is_not ZGname. Abort.

(* Literal environment (hypothesis scans); a local-name environment is skipped. *)
Lemma env_literal_guard : ⊢ P -∗ P.
Proof.
  iStartProof. iIntros "H".
  zesu_env_literal. zesu_envs_record.
  match goal with |- environments.envs_entails ?E _ => set (e := E) end.
  Fail zesu_env_literal. Fail zesu_envs_record.
  unfold e. iExact "H".
Qed.

(* Policy R: mapping keys; policy R': pure-fact keys. *)
Lemma mapping_key_guard : True.
Proof.
  zesu_mapping_key_ok P. Fail zesu_mapping_key_ok (P -∗ P)%I.
  Fail zesu_mapping_key_ok (find_in_context (FindMemMapsTo 8) (fun _ => True : iProp Sigma)%I).
  zesu_pure_fact_key_ok P. Fail zesu_pure_fact_key_ok (P ∗ P)%I.
  exact I.
Qed.

(* Policy B: the instruction-precondition match. *)
Lemma instr_pre_match_guard (A R : iProp Sigma) (T : iProp Sigma -> iProp Sigma) :
  ⊢ zesu_instr_pre_match A R T.
Proof. iStartProof. zesu_instr_pre_match_goal. Abort.
Lemma instr_pre_match_guard_ex (A R : iProp Sigma) (T : Z -> iProp Sigma -> iProp Sigma) :
  ⊢ ∃ x : Z, zesu_instr_pre_match A R (T x).
Proof. iStartProof. zesu_instr_pre_match_goal. Abort.
Lemma instr_pre_match_guard_skip : ⊢ (∃ x : Z, ⌜x = 0⌝ : iProp Sigma)%I.
Proof. iStartProof. Fail zesu_instr_pre_match_goal. Abort.

End guards.

(* Policy Z: the tag-bound closer. *)
Lemma tag_bound_guard : (1 < 2)%Z.
Proof. zesu_tag_bound_goal. reflexivity. Qed.
Lemma tag_bound_guard_skip : (1 <= 2)%Z.
Proof. Fail zesu_tag_bound_goal. discriminate. Qed.

(* Policy P: the Coq-goal route of registered pure facts skips a product. *)
Section pure_fact_products.
Context (Q : Prop) (HQ : SimplAnd Q True).
Context (HF : SimplAnd (forall n : nat, n = n) True).
#[local] Existing Instance HQ.
#[local] Existing Instance HF.
Lemma pure_fact_route_runs : Q.
Proof using HQ Q. zesu_pure_fact_hints_if_enabled. Qed.
Lemma pure_fact_route_skips_product : forall n : nat, n = n.
Proof. Fail zesu_pure_fact_hints_if_enabled. reflexivity. Qed.
End pure_fact_products.
