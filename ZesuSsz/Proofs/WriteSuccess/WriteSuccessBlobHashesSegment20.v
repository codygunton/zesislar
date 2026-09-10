From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_blob_hashes_tail `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x15558 (writeSuccessBlobHashesTailSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput #Hloop".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  destruct remaining as [|remaining'].
  - exfalso. apply H11. bv_solve.
  - iExists
      (tail, bytes, remaining', S processed,
       (processed + S (S remaining'))%nat, base, tt)ₗ.
    liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  all: try lia.
  all: try iFrame.
  all: try bv_solve.
  all: have Hremaining : remaining = O by
    (bv_simplify_arith H11; bv_solve).
  all: subst remaining.
  all: cbn.
  all: try reflexivity.
  all: try (bv_simplify_arith H1; bv_solve).
Qed.
