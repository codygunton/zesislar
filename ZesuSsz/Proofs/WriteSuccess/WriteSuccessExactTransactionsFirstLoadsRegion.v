Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasSignatureEntry WriteSuccessExactTransactionsSignatureFieldEntry
  WriteSuccessExactTransactionsFieldFlagEntry WriteSuccessExactTransactionsFieldFlagRegion
  WriteSuccessExactTransactionsSignatureFlagFrame WriteSuccessExactTransactionsLoadFrame
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsSignatureLoads
  WriteSuccessExactTransactionsFieldLoads WriteSuccessExactTransactionsFlagLoads.

Local Instance transaction_field_load_entry_proper `{!islaG Sigma} `{!threadG} sp row base bytes index :
  Proper (equiv ==> equiv) (transactionFieldLoadEntry sp row base bytes index).
Proof. intros P Q HPQ. unfold transactionFieldLoadEntry. by rewrite HPQ. Qed.

Local Instance transaction_signature_field_retained_proper `{!islaG Sigma} `{!threadG} sp row bytes index :
  Proper (equiv ==> equiv) (transactionSignatureFieldRetained sp row bytes index).
Proof. intros P Q HPQ. unfold transactionSignatureFieldRetained. by rewrite HPQ. Qed.

Local Instance transaction_signature_load_entry_proper `{!islaG Sigma} `{!threadG} sp row base bytes index :
  Proper (equiv ==> equiv) (transactionSignatureLoadEntry sp row base bytes index).
Proof. intros P Q HPQ. unfold transactionSignatureLoadEntry. by rewrite HPQ. Qed.

Lemma transactions_first_loads_region_correct `{!islaG Sigma} `{!threadG}
    sp row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_29.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f68 (transactionFlagLoadPost row base bytes index
    (transactionFieldFlagRetained sp bytes index
      (transactionSignatureFieldRetained sp row bytes index
        (transactionGasSignatureRetained sp bytes index P)))) -∗
  instr_body 0x14f1c (transactionGasLoadEntry row base bytes index
    (transactionGasSignatureCaller sp bytes index
      (transactionSignatureFieldCaller sp bytes index
        (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗ P ∗ True)%I))).
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  iPoseProof (transactions_field_flag_region_correct sp row base bytes index
    (transactionSignatureFieldRetained sp row bytes index
      (transactionGasSignatureRetained sp bytes index P)) with "Hcode Hnext") as "Hfields".
  iAssert (instr_body 0x14f44 (transactionSignatureLoadPost sp row base bytes index
    (transactionSignatureFieldCaller sp bytes index
      (transactionGasSignatureRetained sp bytes index
        (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗ P ∗ True)%I))))%I
    with "[Hfields]" as "HsignatureNext".
  { iApply (instr_pre_wand 0x14f44 0x14f44 false false with "Hfields"); [done | done |].
    iIntros "Hpost".
    iPoseProof (transactions_signature_field_entry sp row base bytes index
      (transactionGasSignatureRetained sp bytes index
        (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗ P ∗ True)%I)
      with "Hpost") as "Hentry".
    iEval (rewrite transactions_gas_signature_retained_frame transactions_signature_flag_frame) in "Hentry".
    iExact "Hentry". }
  iPoseProof (transactions_signature_loads_correct with "Hcode HsignatureNext") as "Hsignature".
  iApply (transactions_gas_loads_correct with "Hcode").
  iApply (instr_pre_wand 0x14f2c 0x14f2c false false with "Hsignature"); [done | done |].
  iIntros "Hpost".
  iPoseProof (transactions_gas_signature_entry sp row base bytes index
    (transactionSignatureFieldCaller sp bytes index
      (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗ P ∗ True)%I)
    with "Hpost") as "Hentry".
  iEval (rewrite transactions_gas_signature_caller_frame) in "Hentry". iExact "Hentry".
Qed.
Print Assumptions transactions_first_loads_region_correct.

