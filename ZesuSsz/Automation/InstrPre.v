Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.

Definition zesu_instr_pre_match `{!islaG Sigma}
    (available requested : iProp Sigma)
    (T : iProp Sigma -> iProp Sigma) : iProp Sigma :=
  ∃ residual, ⌜residual ⊢ (requested -∗ available)⌝ ∗ T residual.

Lemma zesu_instr_pre_match_identity `{!islaG Sigma}
    (available requested : iProp Sigma) (T : iProp Sigma -> iProp Sigma) :
  available = requested ->
  T emp ⊢ zesu_instr_pre_match available requested T.
Proof.
  intros ->. iIntros "HT". iExists emp%I. iSplit.
  - iPureIntro. iIntros "_ Havailable". iExact "Havailable".
  - iExact "HT".
Qed.

Lemma zesu_instr_pre_match_wand `{!islaG Sigma}
    (available requested : iProp Sigma) (T : iProp Sigma -> iProp Sigma) :
  T (requested -∗ available) ⊢
  zesu_instr_pre_match available requested T.
Proof.
  iIntros "HT". iExists (requested -∗ available)%I. iSplit.
  - iPureIntro. iIntros "Hwand". iExact "Hwand".
  - iExact "HT".
Qed.

Lemma subsume_instr_pre_zesu `{!islaG Sigma} `{!threadG}
    A address b1 b2 available requested G :
  (∃ x, ⌜implb b1 (b2 x)⌝ ∗
     zesu_instr_pre_match available (requested x)
       (fun residual => residual ∗ G x))
  ⊢ subsume (instr_pre' b1 address available)
      (fun x : A => instr_pre' (b2 x) address (requested x)) G.
Proof.
  iDestruct 1 as (x Hlater) "Hmatch".
  iDestruct "Hmatch" as (residual Hresidual) "[Hresidual HG]".
  iApply subsume_instr_pre_wand. iExists x. iFrame "HG". iSplit; [done |].
  iApply Hresidual. iExact "Hresidual".
Qed.

Definition subsume_instr_pre_zesu_inst `{!islaG Sigma} `{!threadG} :=
  [instance subsume_instr_pre_zesu].
Global Existing Instance subsume_instr_pre_zesu_inst | 0.

Print Assumptions zesu_instr_pre_match_identity.
Print Assumptions zesu_instr_pre_match_wand.
Print Assumptions subsume_instr_pre_zesu.
