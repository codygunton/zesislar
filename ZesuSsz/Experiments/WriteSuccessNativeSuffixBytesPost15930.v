From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessNativeSuffixBytesBoundaryAdapter.
Require Import ZesuSsz.Experiments.WriteSuccessPost15930Loads.

(** The aggregate frame remains opaque in [P].  These states expose only the
    two post-hash loads and the return-address update. *)
Definition writeSuccessPost15938AggregateSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64),
    writeSuccessPost15938Spec
      ("x2" ↦ᵣ RVal_Bits sp ∗
       "x10" ↦ᵣ RVal_Bits pointer ∗
       "x11" ↦ᵣ RVal_Bits count ∗
       (bv_unsigned sp + 24) ↦ₘ pointer ∗
       (bv_unsigned sp + 16) ↦ₘ count ∗ P))%I.

Global Instance : LithiumUnfold (@writeSuccessPost15938AggregateSpec) := I.

Definition writeSuccessPost1593cAggregateSpec
    `{!islaG Sigma} `{!threadG} (sp pointer count : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (instr_pre 0x1593c
    (reg_col zesu_ram_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (BV 64 0x15938) ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     "x10" ↦ᵣ RVal_Bits pointer ∗
     "x11" ↦ᵣ RVal_Bits count ∗
     (bv_unsigned sp + 24) ↦ₘ pointer ∗
     (bv_unsigned sp + 16) ↦ₘ count ∗ P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessPost1593cAggregateSpec) := I.

Definition writeSuccessPost15934AggregateSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp data size pointer count : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15930) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits pointer ∗
    "x11" ↦ᵣ RVal_Bits size ∗
    (bv_unsigned sp + 24) ↦ₘ pointer ∗
    (bv_unsigned sp + 16) ↦ₘ count ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp + 16 < 0x40000000⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp + 24 < 0x40000000⌝ ∗
    writeSuccessPost1593cAggregateSpec sp pointer count P ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessPost15934AggregateSpec) := I.

Definition writeSuccessPost15930AggregateSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp data size pointer count : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15930) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits data ∗
    "x11" ↦ᵣ RVal_Bits size ∗
    (bv_unsigned sp + 24) ↦ₘ pointer ∗
    (bv_unsigned sp + 16) ↦ₘ count ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp + 16 < 0x40000000⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp + 24 < 0x40000000⌝ ∗
    writeSuccessPost1593cAggregateSpec sp pointer count P ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessPost15930AggregateSpec) := I.

Lemma write_success_post_15934_to_15938
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15938 (writeSuccessPost15938AggregateSpec P) -∗
  instr_body 0x15934 (writeSuccessPost15934AggregateSpec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof "Hlookup" as "#Hlookup15934".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15934".
  iPoseProof ("Hlookup15934" $! 0x15934 with "[]") as "#Hinstr15934".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15934. done. }
  iPoseProof (write_success_post_15934_load_count with "Hinstr15934") as "#Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessPost15934AggregateSpec) in "Hentry".
  iDestruct "Hentry" as
    (sp data size pointer count)
    "(Hsys & H1 & H2 & H10 & H11 & Hpointer & Hcount & %Halign & %Hrange16 & %Hrange24 & Hpost & HP & _)".
  iAssert ("x11" ↦ᵣ: (fun _ => True))%I with "[H11]" as "H11Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists _. iFrame. }
  rewrite /InstrSpecs.Specs.zesu_ld_spec /InstrSpecs.Specs.rv64_ld_spec.
  iApply "Hld".
  iExists count, sp.
  iFrame "Hsys H11Any H2 Hcount".
  iSplit.
  - iPureIntro; exact Halign.
  - iSplit.
    + iPureIntro; exact Hrange16.
    + rewrite instr_pre'_eq. iNext. iIntros "Hload".
  iApply "Hnext".
  iEval (rewrite /writeSuccessPost15938AggregateSpec).
  iExists sp, pointer, count.
  iEval (rewrite /writeSuccessPost15938Spec).
  iEval (rewrite /writeSuccessPost1593cAggregateSpec) in "Hpost".
  iDestruct "Hload" as "(HsysPost & H11Post & H2Post & HcountPost & _)".
  iAssert ("x1" ↦ᵣ: (fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝))%I with "[H1]" as "H1shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iFrame. iPureIntro. bv_solve. }
  iFrame "HsysPost H1shape H2Post H10 H11Post Hpointer HcountPost HP".
  iExact "Hpost".
Qed.

Lemma write_success_post_15930_to_15938
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15938 (writeSuccessPost15938AggregateSpec P) -∗
  instr_body 0x15930 (writeSuccessPost15930AggregateSpec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof (write_success_post_15934_to_15938 P with
    "Hlookup Hnext") as "Hbody15934".
  iPoseProof "Hlookup" as "#Hlookup15930".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15930".
  iPoseProof ("Hlookup15930" $! 0x15930 with "[]") as "#Hinstr15930".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15930. done. }
  iPoseProof (write_success_post_15930_load_pointer with "Hinstr15930") as "#Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessPost15930AggregateSpec) in "Hentry".
  iDestruct "Hentry" as
    (sp data size pointer count)
    "(Hsys & H1 & H2 & H10 & H11 & Hpointer & Hcount & %Halign & %Hrange16 & %Hrange24 & Hpost & HP & _)".
  iAssert ("x10" ↦ᵣ: (fun _ => True))%I with "[H10]" as "H10Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists _. iFrame. }
  rewrite /InstrSpecs.Specs.zesu_ld_spec /InstrSpecs.Specs.rv64_ld_spec.
  iApply "Hld".
  iExists pointer, sp.
  iFrame "Hsys H10Any H2 Hpointer".
  iSplit.
  - iPureIntro; exact Halign.
  - iSplit.
    + iPureIntro; exact Hrange24.
    + rewrite instr_pre'_eq. iNext. iIntros "Hload".
  iApply "Hbody15934".
  iEval (rewrite /writeSuccessPost15934AggregateSpec).
  iExists sp, data, size, pointer, count.
  iDestruct "Hload" as "(HsysPost & H10Post & H2Post & HpointerPost & _)".
  iFrame "HsysPost H1 H2Post H10Post H11 HpointerPost Hcount Hpost HP".
  iPureIntro.
  split; [exact Halign|].
  split; [exact Hrange16|].
  exact Hrange24.
Qed.
