Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsBoundary151dc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsBoundary15200.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Remove Hints writeSuccessAccessEntryStorageOwn_unfold :
  typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_access_lists_chunk_151dc
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  instr_body 0x15200 (writeSuccessAccessListsAt15200Spec x19 P) -∗
  instr_body 0x151dc (writeSuccessAccessListsAt151dcSpec x19 P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hmemcpy Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  run_write_success_access_lists_chunk 0x15200.
  Unshelve. all: try run_write_success_access_lists_return 0x15200.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  iExists
    ((writeSuccessAccessEntryBytes entry ++
      writeSuccessAccessEntriesBytes remaining), tt)ₗ.
  have HprocessedBytes :
      (40 * Z.of_nat (length processed) <=
       Z.of_nat
         (length
           (writeSuccessAccessEntriesBytes
             (processed ++ entry :: remaining))))%Z.
  { rewrite H2 Nat2Z.inj_mul app_length. cbn. lia. }
  have HprocessedRange :
      (0 <= Z.of_nat (length processed) < 2 ^ 64)%Z by lia.
  have HentriesNonempty : processed ++ entry :: remaining <> [].
  { intro Hnil. destruct processed; discriminate. }
  have HbaseUpper := H10 HentriesNonempty.
  have HoffsetRange :
      (0 <= 40 * Z.of_nat (length processed) /\
       base + 40 * Z.of_nat (length processed) < 2 ^ 64)%Z by lia.
  have HsourceAddress :
      bv_unsigned
        (Z_to_bv 64 base +
         bv_extract 0 64
           (bv_sign_extend 128 (Z_to_bv 64 (Z.of_nat (length processed))) *
            bv_sign_extend 128 (BV 64 40))) =
      (base + 40 * Z.of_nat (length processed))%Z.
  { bv_simplify_arith. bv_solve. }
  have HdestinationAddress :
      bv_unsigned (sp + BV 64 1744) =
      (bv_unsigned sp + 1744)%Z by bv_solve.
  rewrite HsourceAddress HdestinationAddress.
  liARun.
  Unshelve. all: try liARun.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try (bv_simplify_arith; lia).
  all: try (replace (bv_unsigned (BV 64 40)) with 40 by vm_compute; lia).
  all: try (change
    (base + 40 * Z.of_nat (length processed) + 40 < (machineRamEnd defaultMap))%Z;
    rewrite H2 Nat2Z.inj_mul app_length in HbaseUpper;
    cbn in HbaseUpper;
    lia).
  Unshelve.
  have HentryLength :
      Z.to_nat (bv_unsigned (BV 64 40)) =
      length (writeSuccessAccessEntryBytes entry).
  { vm_compute. exact (eq_sym (proj1 H0)). }
  iRename select
    ((bv_unsigned sp + 1744) ↦ₘ∗
      take (Z.to_nat (bv_unsigned (BV 64 40)))
        (writeSuccessAccessEntryBytes entry ++
         writeSuccessAccessEntriesBytes remaining))%I into "Hcopied".
  iEval (rewrite (take_app_length' _ _ _ HentryLength)) in "Hcopied".
  iExists
    (tail, savedX22,
     (writeSuccessAccessEntryBytes entry ++
      writeSuccessAccessEntriesBytes remaining),
     writeSuccessAccessEntriesBytes processed,
     writeSuccessAccessEntriesBytes (processed ++ entry :: remaining),
     remaining, processed, (processed ++ entry :: remaining), entry,
     base, tt)ₗ.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.
