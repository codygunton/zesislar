Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderOptionalU64Call.
Lemma optional_valid_none (pointer : bv 64) (bytes : list (bv 8)) :
  bytes !! 8%nat = Some (BV 8 0) -> encoderOptionalU64Valid pointer bytes.
Proof. intros H. rewrite /encoderOptionalU64Valid H. case_decide; done. Qed.
Lemma optional_outcome_none (bytes : list (bv 8)) :
  bytes !! 8%nat = Some (BV 8 0) -> encoderOptionalU64Outcome bytes = None.
Proof. intros H. rewrite /encoderOptionalU64Outcome H. case_decide; done. Qed.
#[export] Hint Resolve optional_valid_none : core.
#[export] Hint Rewrite optional_outcome_none using assumption : lithium_rewrite isla_coq_rewrite.
Global Instance simplify_optional_valid_none (pointer : bv 64) (bytes : list (bv 8))
    `{!TCFastDone (bytes !! 8%nat = Some (BV 8 0))} :
  SimplAndUnsafe (encoderOptionalU64Valid pointer bytes) (bytes !! 8%nat = Some (BV 8 0)).
Proof. unfold SimplAndUnsafe. exact (optional_valid_none pointer bytes). Qed.
Lemma optional_valid_aligned pointer bytes :
  (9 <= length bytes)%nat -> bv_extract 0 3 pointer = BV 3 0 ->
  encoderOptionalU64Valid pointer bytes.
Proof.
  intros Hlength Halign.
  destruct (bytes !! 8%nat) as [tag|] eqn:Htag.
  - rewrite /encoderOptionalU64Valid Htag. case_decide; naive_solver lia.
  - apply lookup_ge_None in Htag. lia.
Qed.
Global Instance simplify_optional_valid_pair pointer bytes
    `{!TCFastDone (length bytes = 16%nat)} :
  SimplAndUnsafe (encoderOptionalU64Valid pointer bytes)
    (bv_extract 0 3 pointer = BV 3 0) | 5.
Proof.
  unfold SimplAndUnsafe. intros Halign. apply optional_valid_aligned; last done.
  unfold TCFastDone in *. lia.
Qed.
Lemma optional_outcome_pair (low high : bv 64) :
  encoderOptionalU64Outcome
    (bv_to_little_endian 8 8 (bv_unsigned low) ++
     bv_to_little_endian 8 8 (bv_unsigned high)) =
  if decide (bv_extract 0 8 high = BV 8 0) then None else Some low.
Proof.
  have Hlength : length (bv_to_little_endian 8 8 (bv_unsigned low)) = 8%nat.
  { apply length_bv_to_little_endian. lia. }
  rewrite /encoderOptionalU64Outcome lookup_app_r; last (rewrite Hlength; lia).
  rewrite Hlength Nat.sub_diag.
  have Htag : bv_to_little_endian 8 8 (bv_unsigned high) !! 0%nat = Some (bv_extract 0 8 high).
  { rewrite /bv_to_little_endian /=. f_equal. bv_solve. }
  rewrite Htag. case_decide; first done.
  f_equal. rewrite take_app Hlength Nat.sub_diag take_0 app_nil_r take_ge; last lia.
  apply Z_to_bv_little_endian_to_bv_to_little_endian; [lia | done].
Qed.
#[export] Hint Rewrite optional_outcome_pair : zesu_payloads lithium_rewrite isla_coq_rewrite.
Lemma simplify_hyp_payload_branches `{!islaG Sigma}
    (condition : Prop) (absent present : spec) (T : iProp Sigma) :
  ((⌜condition⌝ -∗ spec_trace absent -∗ T) ∧
   (⌜¬ condition⌝ -∗ spec_trace present -∗ T)) ⊢
  simplify_hyp ((⌜condition⌝ ∗ spec_trace absent) ∨
    (⌜¬ condition⌝ ∗ spec_trace present)) T.
Proof.
  unfold simplify_hyp. iIntros "Hbranches [(Hcondition & Htrace)| (Hcondition & Htrace)]".
  - iDestruct "Hbranches" as "[Hbranch _]". iApply ("Hbranch" with "Hcondition Htrace").
  - iDestruct "Hbranches" as "[_ Hbranch]". iApply ("Hbranch" with "Hcondition Htrace").
Qed.
Definition simplify_hyp_payload_branches_inst :=
  [instance @simplify_hyp_payload_branches with 0%N].
Global Existing Instance simplify_hyp_payload_branches_inst.
