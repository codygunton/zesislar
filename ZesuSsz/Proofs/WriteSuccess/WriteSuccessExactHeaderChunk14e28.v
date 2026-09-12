Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPayloadCall.

Ltac run_write_success_exact_header_1184 bytes eventTail :=
  lazymatch goal with
  | |- instr_body 0x14e38 _ => idtac
  | _ =>
      first
        [ progress iEval (unfold zesuWriteOutputPayloadCallSpec, zesu_c_call,
            writeSuccessHeaderPayload)
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | bv_solve
        | lia ];
      run_write_success_exact_header_1184 bytes eventTail
  end.

Lemma write_success_exact_header_chunk_14e28
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x14e38
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessExactHeaderEventsAfter1184 sp bytes tail) tail P) -∗
  instr_body 0x14e28
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessExactHeaderEventsAfterTag sp bytes tail) tail P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  iAssert (instr_body 0x14e38
      (writeSuccessExactHeaderAfterCopySpec 152 32 sp bytes
        (writeSuccessExactHeaderEventsAfter1184 sp bytes tail) tail P))%I
    with "[Hnext]" as "HnextSplit".
  { iApply (instr_pre_wand 0x14e38 0x14e38 false false with "Hnext");
      [done | done |].
    iIntros "Hsplit".
    iApply (writeSuccessExactHeaderAfterCopySpec_to_standard with "Hsplit"). }
  iRename "HnextSplit" into "Hnext".
  iEval (unfold writeSuccessExactHeaderEventsAfterTag).
  run_write_success_exact_header_1184 bytes
    (writeSuccessExactHeaderEventsAfter1184 sp bytes tail).
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  liShow.
  iRename select (mmio_range 0x2401a0c0 16)%I into "Hmmio".
  iRename select (spec_trace (writeOutputEvents (sp + BV 64 1184)%bv
    (BV 64 32) (take 32 (drop 152 (take 592 bytes)))
    (writeSuccessExactHeaderEventsAfter1184 sp bytes tail)))%I into "Htrace".
  iRename select ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes)%I into "Hcopy".
  iDestruct (mem_mapsto_array_region 8%N (bv_unsigned sp + 1032)
    (DfracOwn 1) (take 592 bytes) 152 32 with "Hcopy") as
    "[Hprefix [Hpayload Hsuffix]]".
  { rewrite length_take. lia. }
  iExists (writeSuccessExactHeaderEventsAfter1184 sp bytes tail,
    writeSuccessHeaderPayload 152 32 bytes, tt)ₗ.
  have Haddress : bv_unsigned (sp + BV 64 1184)%bv =
      (bv_unsigned sp + 1032 + 152)%Z by bv_solve.
  iEval (rewrite /= -Haddress) in "Hpayload".
  iFrame "Hpayload Hmmio Htrace".
  all: try (unfold writeSuccessHeaderPayload;
    rewrite !length_take !length_drop H0; cbn; lia).
  all: try liARun.
  all: try (vm_compute; done).
  Unshelve.
  all: prepare_sidecond.
  all: try (rewrite (writeSuccessHeaderPayload_length 152 32 bytes H0
    ltac:(lia)); reflexivity).
  all: lia.
Qed.

Print Assumptions write_success_exact_header_chunk_14e28.
