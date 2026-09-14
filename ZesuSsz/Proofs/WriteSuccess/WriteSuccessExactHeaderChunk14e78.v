Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderAutomation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPayloadCall.

Import ListNotations.

Lemma write_success_exact_header_chunk_14e78_core
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x14e78 (writeSuccessExactHeaderFinalSpec sp bytes tail P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup #Hcode #Houtput".
  iEval (unfold writeSuccessExactHeaderFinalSpec, writeSuccessExactHeaderEventsAfter1300). run_exact_header_call.
  Unshelve.
  all: try prepare_sidecond; try assumption; try bv_solve; try lia; try iFrame.
  Unshelve. liShow.
  iDestruct select (mmio_range (machineOutputAddress defaultMap) 16)%I as "Hmmio".
  iDestruct select (spec_trace (writeOutputEvents (sp + BV 64 1556)%bv (BV 64 32) (writeSuccessHeaderPayload 524 32 bytes) tail))%I as "Htrace".
  iDestruct select ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes)%I as "Hcopy".
  iDestruct (mem_mapsto_array_region 8%N (bv_unsigned sp + 1032) (DfracOwn 1) (take 592 bytes) 524 32 with "Hcopy") as "[Hprefix [Hpayload Hsuffix]]".
  { rewrite length_take H0. vm_compute. lia. }
  iExists (tail, writeSuccessHeaderPayload 524 32 bytes, tt)ₗ.
  have Haddress : bv_unsigned (sp + BV 64 1556)%bv = (bv_unsigned sp + 1032 + 524)%Z by bv_solve.
  iEval (rewrite /= -Haddress) in "Hpayload". iFrame "Hpayload Hmmio Htrace".
  all: try (rewrite (writeSuccessHeaderPayload_length 524 32 bytes H0 ltac:(lia)); reflexivity).
  all: try liARun.
  Unshelve.
  all: prepare_sidecond; try assumption; try bv_solve; try lia.
  all: try (rewrite (writeSuccessHeaderPayload_length 524 32 bytes H0 ltac:(lia)); reflexivity).
  Unshelve.
  all: rewrite /writeSuccessExactHeaderPost.
  all: iDestruct select (reg_col zesu_ram_sys_regs)%I as "HsysPost"; iFrame "HsysPost".
  all: iDestruct select (reg_col ((KindReg "x8", ExactShape _) :: _))%I as "Hsaved".
  all: iPoseProof (reg_col_exact_bv_to_bits
    ["x8"; "x9"; "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]
    [b9; b10; b11; b12; b13; b14; b15; b16; b17; b18; b19; b20]
    with "Hsaved") as "HsavedBits"; first reflexivity.
  all: iEval (unfold reg_col; cbn) in "HsavedBits".
  all: iDestruct select (reg_col _)%I as "Hregs1"; iEval (unfold reg_col; cbn) in "Hregs1".
  all: iDestruct select (reg_col _)%I as "Hregs2"; iEval (unfold reg_col; cbn) in "Hregs2".
  all: iDestruct "Hregs1" as "(Hr1 & Hr12 & Hr13 & Hr14 & Hr15 & Hr16 & Hr17 & Hr5 & Hr6 & Hr7 & Hr28 & Hr29 & Hr30 & Hr31 & _)".
  all: iDestruct "Hregs2" as "(Hr3 & Hr4 & _)".
  all: iDestruct "HsavedBits" as "(Hr8 & Hr9 & Hr18 & Hr19 & Hr20 & Hr21 & Hr22 & Hr23 & Hr24 & Hr25 & Hr26 & Hr27 & _)".
  all: iDestruct select (bv_unsigned LET0 ↦ₘ∗ writeSuccessHeaderPayload 524 32 bytes)%I as "HpayloadPost".
  all: iEval (replace (bv_unsigned LET0) with (bv_unsigned sp + 1556)%Z by bv_solve) in "HpayloadPost".
  all: iEval (replace (bv_unsigned sp + 1032 + 1 * 556%nat)%Z with (bv_unsigned sp + 1588)%Z by lia) in "Hsuffix".
  all: iEval (unfold writeSuccessHeaderRegShapes, writeSuccessHeaderRegisters, reg_col; cbn).
  all: try iFrame; repeat iSplit; try iFrame; try iPureIntro; try assumption; try bv_solve; try lia.
  all: iExact "Hmmio".
Qed.

Lemma write_success_exact_header_chunk_14e78
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x14e78
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessExactHeaderEventsAfter1300 sp bytes tail) tail P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput".
  iPoseProof (write_success_exact_header_chunk_14e78_core sp bytes tail P
    with "Hlookup Hcode Houtput") as "Hcore".
  iApply (instr_pre_wand 0x14e78 0x14e78 false false with "Hcore");
    [done | done |].
  iIntros "Hstandard".
  iApply (writeSuccessHeaderAfterCopy_to_exact_final with "Hstandard").
Qed.

Print Assumptions write_success_exact_header_chunk_14e78.
