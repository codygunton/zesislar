Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.EntryPreparation.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Automation.SealedCoverage.
From iris.proofmode Require Import tactics environments.
Open Scope Z_scope.
Definition folded_fact (n : Z) : Prop := 2 <= n /\ n <= 4.
Definition fact_entry `{!islaG Sigma} (n : Z) (P : iProp Sigma) : iProp Sigma := (⌜folded_fact n⌝ ∗ P)%I.
Definition nested_entry `{!islaG Sigma} (P : iProp Sigma) : iProp Sigma := (∃ n : Z, fact_entry n P)%I.
Definition unrelated_seal `{!islaG Sigma} (P : iProp Sigma) : iProp Sigma := P.
Global Opaque unrelated_seal.
Definition registered_companion `{!islaG Sigma} (P Q : iProp Sigma) : iProp Sigma := (P ∗ unrelated_seal Q)%I.
Global Instance : LithiumUnfold (@registered_companion) := I.
Global Typeclasses Opaque registered_companion.
Definition opaque_registered `{!islaG Sigma} (P : iProp Sigma) : iProp Sigma := P.
Global Instance : LithiumUnfold (@opaque_registered) := I.
Global Typeclasses Opaque opaque_registered.
Global Opaque opaque_registered.
Definition concrete_entry_bytes : list (bv 8) := [BV 8 1; BV 8 2; BV 8 3; BV 8 4].
Definition registered_code_companion `{!islaG Sigma} `{!threadG}
 (P : iProp Sigma) (lookup : Z -> option isla_trace) : iProp Sigma := (P ∗ instr_lookup_resources lookup)%I.
Global Instance : LithiumUnfold (@registered_code_companion) := I.
Global Typeclasses Opaque registered_code_companion.
Definition declared_entry_seal `{!islaG Sigma} (P : iProp Sigma) : iProp Sigma := P.
Global Instance : LithiumUnfold (@declared_entry_seal) := I.
Global Typeclasses Opaque declared_entry_seal.
Global Instance declared_entry_seal_instance `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
 ZesuSealed (declared_entry_seal P) P [] [].
Proof. constructor. reflexivity. Qed.
Definition unregistered_predicate_companion `{!islaG Sigma} `{!threadG}
 (P Q : iProp Sigma) : iProp Sigma := (("x11" ↦ᵣ: (fun _ => P)) ∗ Q)%I.
Section Tests.
Context `{!islaG Sigma} `{!threadG}.
Lemma folded_entry_preparation (n : Z) (P : iProp Sigma) (t : isla_trace) :
 fact_entry n P -∗ (⌜0 <= n⌝ ∗ P -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hentry Hnext". repeat zesu_prepare_entry_facts.
 iApply "Hnext". iFrame. iPureIntro. lia. Qed.
Lemma nested_entry_preservation (P Q : iProp Sigma) (t : isla_trace) :
 nested_entry P -∗ unrelated_seal Q -∗
 (P ∗ unrelated_seal Q -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hentry Hunrelated Hnext". repeat zesu_prepare_entry_facts.
 iApply "Hnext". iFrame. Qed.
Lemma opaque_entry_rejection (P : iProp Sigma) (t : isla_trace) :
 unrelated_seal P -∗ (unrelated_seal P -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hopaque Hnext". Fail zesu_prepare_entry_facts.
 iApply "Hnext". iFrame. Qed.
Lemma unresolved_entry_rejection (P : iProp Sigma) (t : isla_trace) :
 P -∗ (P -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "HP Hnext". let unresolved := open_constr:(_ : iProp Sigma) in
 tryif zesu_entry_has_pure_fact unresolved then fail 1 "unresolved entry selected" else idtac.
 Fail zesu_prepare_entry_facts. iApply "Hnext". iFrame. Qed.
Lemma irrelevant_package_rejection (P : iProp Sigma) (t : isla_trace) :
 (P ∗ True) -∗ (P ∗ True -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hpackage Hnext". Fail zesu_prepare_entry_facts.
 iApply "Hnext". iFrame. Qed.
Lemma non_execution_goal_rejection (n : Z) (P : iProp Sigma) :
 fact_entry n P -∗ fact_entry n P.
Proof. iIntros "Hentry". Fail zesu_prepare_entry_facts. iFrame. Qed.
Lemma registered_companion_preservation (n : Z) (P Q : iProp Sigma) (t : isla_trace) :
 fact_entry n (registered_companion P Q) -∗
 (P ∗ unrelated_seal Q -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hentry Hnext". repeat zesu_prepare_entry_facts.
 iMatchHyp ltac:(fun H assertion => constr_eq assertion constr:((unrelated_seal Q)%I)).
 iApply "Hnext". iFrame. Qed.
Lemma selected_register_predicate (n : Z) (P Q : iProp Sigma) (t : isla_trace) :
 fact_entry n (registered_companion ("x11" ↦ᵣ: (fun _ => P)) Q) -∗
 (∀ value : valu, "x11" ↦ᵣ value ∗ P ∗ unrelated_seal Q -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hentry Hnext". repeat zesu_prepare_entry_facts.
 iApply "Hnext". iFrame. Qed.
Lemma opaque_registered_preservation (n : Z) (P : iProp Sigma) (t : isla_trace) :
 fact_entry n (opaque_registered P) -∗
 (opaque_registered P -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hentry Hnext". repeat zesu_prepare_entry_facts.
 iMatchHyp ltac:(fun H assertion => constr_eq assertion constr:((opaque_registered P)%I)).
 iApply "Hnext". iFrame. Qed.
Lemma concrete_array_preservation (n base : Z) (t : isla_trace) :
 fact_entry n (base ↦ₘ∗ concrete_entry_bytes) -∗
 (base ↦ₘ∗ concrete_entry_bytes -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hentry Hnext". repeat zesu_prepare_entry_facts.
 iMatchHyp ltac:(fun H assertion => constr_eq assertion constr:((base ↦ₘ∗ concrete_entry_bytes)%I)).
 iApply "Hnext". iFrame. Qed.
Lemma code_resource_preservation (n : Z) (P : iProp Sigma)
 (lookup : Z -> option isla_trace) (t : isla_trace) :
 fact_entry n (registered_code_companion P lookup) -∗
 (P ∗ instr_lookup_resources lookup -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hentry Hnext". repeat zesu_prepare_entry_facts.
 iMatchHyp ltac:(fun H assertion => constr_eq assertion constr:((instr_lookup_resources lookup)%I)).
 iApply "Hnext". iFrame. Qed.
Lemma declared_seal_preservation (n : Z) (P : iProp Sigma) (t : isla_trace) :
 fact_entry n (declared_entry_seal P) -∗
 (declared_entry_seal P -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hentry Hnext". repeat zesu_prepare_entry_facts.
 iMatchHyp ltac:(fun H assertion => constr_eq assertion constr:((declared_entry_seal P)%I)).
 iApply "Hnext". iFrame. Qed.
Lemma nested_register_predicate_preservation (n : Z) (P Q : iProp Sigma) (t : isla_trace) :
 fact_entry n (unregistered_predicate_companion P Q) -∗
 (unregistered_predicate_companion P Q -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hentry Hnext". repeat zesu_prepare_entry_facts.
 iMatchHyp ltac:(fun H assertion => constr_eq assertion constr:((unregistered_predicate_companion P Q)%I)).
 iApply "Hnext". iFrame. Qed.
Lemma unbundled_shape_entry (value : valu) (t : isla_trace) :
 ⌜valu_has_shape value (BitsShape 64)⌝ -∗
 (⌜valu_has_shape value (BitsShape 64)⌝ -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hshape Hnext". time zesu_prepare_entry_facts.
 match goal with Hshape : valu_has_shape value (BitsShape 64) |- _ => idtac end.
 iApply "Hnext". iPureIntro. assumption. Qed.
Lemma unbundled_shape_preserves_resources (value : valu) (base : Z)
 (word : bv 64) (Q : iProp Sigma) (lookup : Z -> option isla_trace)
 (t : isla_trace) :
 ⌜valu_has_shape value (BitsShape 64)⌝ -∗
 base ↦ₘ∗ concrete_entry_bytes -∗ (base + 8) ↦ₘ word -∗
 reg_col zesu_ram_sys_regs -∗ declared_entry_seal Q -∗ instr_lookup_resources lookup -∗
 (⌜valu_has_shape value (BitsShape 64)⌝ ∗ base ↦ₘ∗ concrete_entry_bytes ∗
  (base + 8) ↦ₘ word ∗ reg_col zesu_ram_sys_regs ∗ declared_entry_seal Q ∗
  instr_lookup_resources lookup -∗ WPasm t) -∗ WPasm t.
Proof. iIntros "Hshape Harray Hword Hregs Hseal Hcode Hnext".
 time zesu_prepare_entry_facts.
 match goal with Hshape : valu_has_shape value (BitsShape 64) |- _ => idtac end.
 let owned := iTypeOf "Harray" in lazymatch owned with Some (_, ?P) => constr_eq P constr:((base ↦ₘ∗ concrete_entry_bytes)%I) end.
 let owned := iTypeOf "Hword" in lazymatch owned with Some (_, ?P) => constr_eq P constr:(((base + 8) ↦ₘ word)%I) end.
 let owned := iTypeOf "Hregs" in lazymatch owned with Some (_, ?P) => constr_eq P constr:((reg_col zesu_ram_sys_regs)%I) end.
 let owned := iTypeOf "Hseal" in lazymatch owned with Some (_, ?P) => constr_eq P constr:((declared_entry_seal Q)%I) end.
 let owned := iTypeOf "Hcode" in lazymatch owned with Some (_, ?P) => constr_eq P constr:((instr_lookup_resources lookup)%I) end.
 iApply "Hnext". iFrame. iPureIntro. assumption. Qed.
End Tests.
Print Assumptions folded_entry_preparation.
Print Assumptions nested_entry_preservation.
Print Assumptions opaque_entry_rejection.
Print Assumptions unresolved_entry_rejection.

Print Assumptions irrelevant_package_rejection.
Print Assumptions non_execution_goal_rejection.

Print Assumptions registered_companion_preservation.
Print Assumptions selected_register_predicate.

Print Assumptions opaque_registered_preservation.

Print Assumptions concrete_array_preservation.
Print Assumptions code_resource_preservation.
Print Assumptions declared_seal_preservation.
Print Assumptions nested_register_predicate_preservation.

Print Assumptions unbundled_shape_entry.
Print Assumptions unbundled_shape_preserves_resources.
