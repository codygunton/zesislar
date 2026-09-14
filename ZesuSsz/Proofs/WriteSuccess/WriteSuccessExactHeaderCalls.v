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

Ltac prove_exact_header_stack_call sp bytes tail P next offset width data eventTail :=
  iAssert (instr_body next
      (writeSuccessExactHeaderAfterCopySpec offset width sp bytes eventTail
        tail P))%I with "[Hnext]" as "HnextSplit";
  [ iApply (instr_pre_wand next next false false with "Hnext");
    [done | done |];
    iIntros "Hsplit";
    iApply (writeSuccessExactHeaderAfterCopySpec_to_standard with "Hsplit")
  | ];
  iRename "HnextSplit" into "Hnext";
  run_exact_header_call_until next.

Lemma write_success_exact_header_chunk_14e38
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x14e48
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessExactHeaderEventsAfter1216 sp bytes tail) tail P) -∗
  instr_body 0x14e38
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessExactHeaderEventsAfter1184 sp bytes tail) tail P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  iEval (unfold writeSuccessExactHeaderEventsAfter1184).
  prove_exact_header_stack_call sp bytes tail P
    0x14e48 184%nat 20%nat (sp + BV 64 1216)%bv
    (writeSuccessExactHeaderEventsAfter1216 sp bytes tail).
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  liShow.
  iRename select (mmio_range (machineOutputAddress defaultMap) 16)%I into "Hmmio".
  iRename select (spec_trace (writeOutputEvents (sp + BV 64 1216)%bv
    (BV 64 20) (writeSuccessHeaderPayload 184 20 bytes)
    (writeSuccessExactHeaderEventsAfter1216 sp bytes tail)))%I into "Htrace".
  iRename select ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes)%I into "Hcopy".
  iDestruct (mem_mapsto_array_region 8%N (bv_unsigned sp + 1032)
    (DfracOwn 1) (take 592 bytes) 184 20 with "Hcopy") as
    "[Hprefix [Hpayload Hsuffix]]".
  { rewrite length_take H0. vm_compute. lia. }
  iExists (writeSuccessExactHeaderEventsAfter1216 sp bytes tail,
    writeSuccessHeaderPayload 184 20 bytes, tt)ₗ.
  have Haddress : bv_unsigned (sp + BV 64 1216)%bv =
      (bv_unsigned sp + 1032 + 184)%Z by bv_solve.
  iEval (rewrite /= -Haddress) in "Hpayload".
  iFrame "Hpayload Hmmio Htrace".
  all: try (rewrite (writeSuccessHeaderPayload_length 184 20 bytes H0
    ltac:(lia)); reflexivity).
  all: try liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (rewrite (writeSuccessHeaderPayload_length 184 20 bytes H0
    ltac:(lia)); reflexivity).
  all: vm_compute; lia.
Qed.

Print Assumptions write_success_exact_header_chunk_14e38.

Lemma write_success_exact_header_chunk_14e48
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x14e58
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessExactHeaderEventsAfter1236 sp bytes tail) tail P) -∗
  instr_body 0x14e48
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessExactHeaderEventsAfter1216 sp bytes tail) tail P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  iEval (unfold writeSuccessExactHeaderEventsAfter1216).
  prove_exact_header_stack_call sp bytes tail P
    0x14e58 204%nat 32%nat (sp + BV 64 1236)%bv
    (writeSuccessExactHeaderEventsAfter1236 sp bytes tail).
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. liShow.
  iRename select (mmio_range (machineOutputAddress defaultMap) 16)%I into "Hmmio".
  iRename select (spec_trace (writeOutputEvents (sp + BV 64 1236)%bv
    (BV 64 32) (writeSuccessHeaderPayload 204 32 bytes)
    (writeSuccessExactHeaderEventsAfter1236 sp bytes tail)))%I into "Htrace".
  iRename select ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes)%I into "Hcopy".
  iDestruct (mem_mapsto_array_region 8%N (bv_unsigned sp + 1032)
    (DfracOwn 1) (take 592 bytes) 204 32 with "Hcopy") as
    "[Hprefix [Hpayload Hsuffix]]".
  { rewrite length_take H0. vm_compute. lia. }
  iExists (writeSuccessExactHeaderEventsAfter1236 sp bytes tail,
    writeSuccessHeaderPayload 204 32 bytes, tt)ₗ.
  have Haddress : bv_unsigned (sp + BV 64 1236)%bv =
      (bv_unsigned sp + 1032 + 204)%Z by bv_solve.
  iEval (rewrite /= -Haddress) in "Hpayload".
  iFrame "Hpayload Hmmio Htrace".
  all: try (rewrite (writeSuccessHeaderPayload_length 204 32 bytes H0
    ltac:(lia)); reflexivity).
  all: try liARun.
  Unshelve. all: prepare_sidecond.
  all: try (rewrite (writeSuccessHeaderPayload_length 204 32 bytes H0
    ltac:(lia)); reflexivity).
  all: vm_compute; lia.
Qed.

Lemma write_success_exact_header_chunk_14e58
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x14e68
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessExactHeaderEventsAfter1268 sp bytes tail) tail P) -∗
  instr_body 0x14e58
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessExactHeaderEventsAfter1236 sp bytes tail) tail P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  iEval (unfold writeSuccessExactHeaderEventsAfter1236).
  prove_exact_header_stack_call sp bytes tail P
    0x14e68 236%nat 32%nat (sp + BV 64 1268)%bv
    (writeSuccessExactHeaderEventsAfter1268 sp bytes tail).
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. liShow.
  iRename select (mmio_range (machineOutputAddress defaultMap) 16)%I into "Hmmio".
  iRename select (spec_trace (writeOutputEvents (sp + BV 64 1268)%bv
    (BV 64 32) (writeSuccessHeaderPayload 236 32 bytes)
    (writeSuccessExactHeaderEventsAfter1268 sp bytes tail)))%I into "Htrace".
  iRename select ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes)%I into "Hcopy".
  iDestruct (mem_mapsto_array_region 8%N (bv_unsigned sp + 1032)
    (DfracOwn 1) (take 592 bytes) 236 32 with "Hcopy") as
    "[Hprefix [Hpayload Hsuffix]]".
  { rewrite length_take H0. vm_compute. lia. }
  iExists (writeSuccessExactHeaderEventsAfter1268 sp bytes tail,
    writeSuccessHeaderPayload 236 32 bytes, tt)ₗ.
  have Haddress : bv_unsigned (sp + BV 64 1268)%bv =
      (bv_unsigned sp + 1032 + 236)%Z by bv_solve.
  iEval (rewrite /= -Haddress) in "Hpayload".
  iFrame "Hpayload Hmmio Htrace".
  all: try (rewrite (writeSuccessHeaderPayload_length 236 32 bytes H0
    ltac:(lia)); reflexivity).
  all: try liARun.
  Unshelve. all: prepare_sidecond.
  all: try (rewrite (writeSuccessHeaderPayload_length 236 32 bytes H0
    ltac:(lia)); reflexivity).
  all: vm_compute; lia.
Qed.

Lemma write_success_exact_header_chunk_14e68
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x14e78
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessExactHeaderEventsAfter1300 sp bytes tail) tail P) -∗
  instr_body 0x14e68
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessExactHeaderEventsAfter1268 sp bytes tail) tail P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  iEval (unfold writeSuccessExactHeaderEventsAfter1268).
  prove_exact_header_stack_call sp bytes tail P
    0x14e78 268%nat 256%nat (sp + BV 64 1300)%bv
    (writeSuccessExactHeaderEventsAfter1300 sp bytes tail).
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. liShow.
  iRename select (mmio_range (machineOutputAddress defaultMap) 16)%I into "Hmmio".
  iRename select (spec_trace (writeOutputEvents (sp + BV 64 1300)%bv
    (BV 64 256) (writeSuccessHeaderPayload 268 256 bytes)
    (writeSuccessExactHeaderEventsAfter1300 sp bytes tail)))%I into "Htrace".
  iRename select ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes)%I into "Hcopy".
  iDestruct (mem_mapsto_array_region 8%N (bv_unsigned sp + 1032)
    (DfracOwn 1) (take 592 bytes) 268 256 with "Hcopy") as
    "[Hprefix [Hpayload Hsuffix]]".
  { rewrite length_take H0. vm_compute. lia. }
  iExists (writeSuccessExactHeaderEventsAfter1300 sp bytes tail,
    writeSuccessHeaderPayload 268 256 bytes, tt)ₗ.
  have Haddress : bv_unsigned (sp + BV 64 1300)%bv =
      (bv_unsigned sp + 1032 + 268)%Z by bv_solve.
  iEval (rewrite /= -Haddress) in "Hpayload".
  iFrame "Hpayload Hmmio Htrace".
  all: try (rewrite (writeSuccessHeaderPayload_length 268 256 bytes H0
    ltac:(lia)); reflexivity).
  all: try liARun.
  Unshelve. all: prepare_sidecond.
  all: try (rewrite (writeSuccessHeaderPayload_length 268 256 bytes H0
    ltac:(lia)); reflexivity).
  all: vm_compute; lia.
Qed.

Print Assumptions write_success_exact_header_chunk_14e48.
Print Assumptions write_success_exact_header_chunk_14e58.
Print Assumptions write_success_exact_header_chunk_14e68.
