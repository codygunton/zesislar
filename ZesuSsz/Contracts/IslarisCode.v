From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Export InstrSpecs.Lookup.

Lemma Z_to_bv_add (n : N) (left right : Z) :
  (Z_to_bv n left + Z_to_bv n right)%bv = Z_to_bv n (left + right).
Proof.
  apply bv_eq. rewrite bv_add_unsigned !Z_to_bv_unsigned.
  bv_wrap_simplify_solve.
Qed.

Set Default Proof Using "Type".

Section automation.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma subsume_instr_pre_wand A address available_l requested_l
      available requested G :
    (∃ x,
      ⌜implb available_l (requested_l x)⌝ ∗
      (requested x -∗ available) ∗ G x)
    ⊢ subsume (instr_pre' available_l address available)
        (fun x : A => instr_pre' (requested_l x) address (requested x)) G.
  Proof.
    iDestruct 1 as (x Hlater) "(Hwand & HG)".
    iIntros "Hpre". iExists x. iFrame "HG".
    iApply (instr_pre_wand with "Hpre Hwand"); [exact Hlater | reflexivity].
  Qed.

  Definition subsume_instr_pre_wand_inst :=
    [instance subsume_instr_pre_wand].

  Lemma subsume_instr_some_pre A address trace requested_l requested G :
    (∃ x,
      (requested x -∗
       arch_pc_reg ↦ᵣ RVal_Bits (Z_to_bv 64 address) -∗ WPasm trace) ∗
      G x)
    ⊢ subsume (instr address (Some trace))
        (fun x : A => instr_pre' (requested_l x) address (requested x)) G.
  Proof.
    iDestruct 1 as (x) "(Hwp & HG)".
    iIntros "Hinstr". iExists x. iFrame "HG".
    iApply (instr_pre_intro_Some with "Hinstr Hwp").
  Qed.

  Definition subsume_instr_some_pre_inst :=
    [instance subsume_instr_some_pre].
End automation.
