From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderU256.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk151a0MvSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk151a0To151a4Return.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Remove Hints find_body_a151a4_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_151a0_to_151a4
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x151a4 (writeSuccessTransactionsAt151a4Spec P) -∗
  instr_body 0x151a0 (writeSuccessTransactionsAt151a0Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try prepare_sidecond; try assumption; try bv_solve; try lia.
  Unshelve.
  iDestruct select (base ↦ₘ∗ prefix ∗ _)%I as
    "(HbasePrefix & HbaseSuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & #Hinvariant & Hexit & _)".
  iPoseProof "Hinvariant" as "#HinvCopy".
  iEval
    (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
    in "HinvCopy".
  iDestruct "HinvCopy" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & %Hmax & _)".
  have Hsp128 : bv_unsigned (sp + 128) = bv_unsigned sp + 128 by
    (rewrite bv_add_unsigned bv_unsigned_BV;
     apply bv_wrap_small;
     pose proof (bv_unsigned_in_range 64 sp);
     pose proof (bv_unsigned_in_range 64 (BV 64 128));
     unfold bv_modulus in *; cbn in *; lia).
  have Hextract128 : bv_extract 0 3 (sp + 128) = 0%bv by bv_solve.
  iRename select (reg_col zesu_ram_sys_regs)%I into "HsysFinal".
  iRename select (reg_col _)%I into "HotherFinal".
  iRename select ("x5" ↦ᵣ _)%I into "Hx5".
  iRename select ("x11" ↦ᵣ _)%I into "Hx11".
  iAssert (writeSuccessTransactionsMachine151a4
    sp base transactions processed transaction)%I
    with "[-HbasePrefix HbaseSuffix Hprocessed Htransaction Hremaining Hmmio
      Htrace HP Hinvariant Hexit]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine151a4.
    iSplitL "HsysFinal"; [iExact "HsysFinal" |].
    iSplitL "HotherFinal"; [iExact "HotherFinal" |].
    unLET; iFrame.
    iSplitL "Hx5".
    - iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
      iExists (RVal_Bits b). iSplitL "Hx5"; [iExact "Hx5"|].
      iPureIntro. cbn. reflexivity.
    - iEval (cbn) in "Hx11".
      set v := WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 56.
      have Hv : (v + 0)%bv = v by
        (apply (bv_add_0_r v (bv_0 64)); apply bv_0_unsigned).
      iEval (rewrite Hv) in "Hx11". iExact "Hx11". }
  iAssert (writeSuccessTransactions151a4Outer P sp base transaction
    transactions processed remaining bytes prefix suffix tail)%I with
    "[HbasePrefix HbaseSuffix Hprocessed Htransaction Hremaining Hmmio Htrace
      HP Hinvariant Hexit]" as "Houter".
  { rewrite /writeSuccessTransactions151a4Outer
      /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff.
    iFrame. done. }
  iPoseProof (write_success_transactions_chunk_151a0_to_151a4_return P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "[] [] [] HmachineFinal Houter") as "Hreturn".
  - iPureIntro. exact Hextract128.
  - iPureIntro. assumption.
  - iPureIntro. assumption.
  - rewrite /writeSuccessTransactionsAt151a4Spec.
    iExact "Hreturn".
Qed.
