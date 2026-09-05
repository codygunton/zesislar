From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.

Definition writeSuccessTransactionsPost15690ZeroSpec
    `{!islaG Sigma} `{!threadG} (pc : Z) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗
   instr_pre (pc + 88)
     (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗ True))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15690ZeroSpec) := I.

Lemma write_success_transactions_zero_bv :
  Z_to_bv 64 (Z.of_nat 0) = BV 64 0.
Proof. bv_solve. Qed.

Lemma write_success_transactions_post_15690_zero_spec
    `{!islaG Sigma} `{!threadG} :
  instr 0x15690 (Some IslaTraces.write_success_89.a15690.a15690) -∗
  instr_body 0x15690 (writeSuccessTransactionsPost15690ZeroSpec 0x15690).
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.

Lemma write_success_transactions_post_15690_zero
    `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_pre 0x156e8
    (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗ True) -∗
  instr_body 0x15690
    (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗ True).
Proof.
  iStartProof. iIntros "#Hlookup Hzero".
  iPoseProof "Hlookup" as "#Hlookup15690".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15690".
  iPoseProof ("Hlookup15690" $! 0x15690 with "[]") as "#Hinstr15690".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15690.
    done. }
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15690)
    in "Hinstr15690".
  iPoseProof (write_success_transactions_post_15690_zero_spec
    with "Hinstr15690") as "Hbranch".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iDestruct "Hentry" as "(Hsys & H9 & _)".
  iEval (rewrite /writeSuccessTransactionsPost15690ZeroSpec).
  iApply "Hbranch".
  iFrame "Hsys H9".
  iEval (rewrite -instr_pre'_eq) in "Hzero".
  iExact "Hzero".
Qed.
