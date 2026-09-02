From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundarySpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1501c.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Definition writeSuccessTransactionsAt14fc8Prefix
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactionsMachine14fc8
     sp base transactions processed transaction ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14fc8Prefix) := I.

Lemma write_success_transactions_chunk_14fc8_prefix
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1501c (writeSuccessTransactionsAt1501cSpec P) -∗
  instr_body 0x14fc8 (writeSuccessTransactionsAt14fc8Prefix P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
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
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  have HcurrentUnsigned :
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) =
      base + 288 * length processed by bv_solve.
  have Haddress268 :
      bv_unsigned
        (Z_to_bv 64 (base + 288 * length processed) + 268) =
      base + 288 * length processed + 268 by bv_solve.
  have Haddress269 :
      bv_unsigned
        (Z_to_bv 64 (base + 288 * length processed) + 269) =
      base + 288 * length processed + 269 by bv_solve.
  have Haddress270 :
      bv_unsigned
        (Z_to_bv 64 (base + 288 * length processed) + 270) =
      base + 288 * length processed + 270 by bv_solve.
  have Haddress271 :
      bv_unsigned
        (Z_to_bv 64 (base + 288 * length processed) + 271) =
      base + 288 * length processed + 271 by bv_solve.
  have Haddress32 :
      bv_unsigned
        (Z_to_bv 64 (base + 288 * length processed) + 32) =
      base + 288 * length processed + 32 by bv_solve.
  have Hindex268 :
      Z.to_nat ((bv_unsigned LET12 -
        (base + 288 * length processed)) `div` 1) = 268%nat.
  { unfold LET12. rewrite Haddress268.
    replace ((base + 288 * length processed + 268 -
      (base + 288 * length processed)) `div` 1)%Z with 268%Z by lia.
    reflexivity. }
  have Hindex269 :
      Z.to_nat ((bv_unsigned LET17 -
        (base + 288 * length processed)) `div` 1) = 269%nat.
  { unfold LET17. rewrite Haddress269.
    replace ((base + 288 * length processed + 269 -
      (base + 288 * length processed)) `div` 1)%Z with 269%Z by lia.
    reflexivity. }
  have Hindex270 :
      Z.to_nat ((bv_unsigned LET22 -
        (base + 288 * length processed)) `div` 1) = 270%nat.
  { unfold LET22. rewrite Haddress270.
    replace ((base + 288 * length processed + 270 -
      (base + 288 * length processed)) `div` 1)%Z with 270%Z by lia.
    reflexivity. }
  have Hindex271 :
      Z.to_nat ((bv_unsigned LET27 -
        (base + 288 * length processed)) `div` 1) = 271%nat.
  { unfold LET27. rewrite Haddress271.
    replace ((base + 288 * length processed + 271 -
      (base + 288 * length processed)) `div` 1)%Z with 271%Z by lia.
    reflexivity. }
  have Hindex32 :
      Z.to_nat ((bv_unsigned LET52 -
        (base + 288 * length processed)) `div` 1) = 32%nat.
  { unfold LET52. rewrite Haddress32.
    replace ((base + 288 * length processed + 32 -
      (base + 288 * length processed)) `div` 1)%Z with 32%Z by lia.
    reflexivity. }
  have Hbyte268 : vmem =
      WriteSuccessTransactionsSpec.writeSuccessTransactionByte
        transaction 268.
  { rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionByte.
    rewrite Hindex268 in H15. rewrite H15. reflexivity. }
  have Hbyte269 : vmem0 =
      WriteSuccessTransactionsSpec.writeSuccessTransactionByte
        transaction 269.
  { rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionByte.
    rewrite Hindex269 in H19. rewrite H19. reflexivity. }
  have Hbyte270 : vmem1 =
      WriteSuccessTransactionsSpec.writeSuccessTransactionByte
        transaction 270.
  { rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionByte.
    rewrite Hindex270 in H23. rewrite H23. reflexivity. }
  have Hbyte271 : vmem2 =
      WriteSuccessTransactionsSpec.writeSuccessTransactionByte
        transaction 271.
  { rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionByte.
    rewrite Hindex271 in H27. rewrite H27. reflexivity. }
  have Hbyte32 : vmem3 =
      WriteSuccessTransactionsSpec.writeSuccessTransactionByte
        transaction 32.
  { rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionByte.
    rewrite Hindex32 in H41. rewrite H41. reflexivity. }
  subst vmem vmem0 vmem1 vmem2 vmem3.
  iRename select
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)%I
    into "Harray".
  iRename select
    (writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    into "Hframe".
  iExists (tail, suffix, prefix, bytes, remaining, transactions,
    transaction, sp, tt)ₗ.
  iSplitR "Harray Hframe".
  -
    iIntros "(Hsys & Hx10 & Hx18 & Hx20 & Hx29)";
    rewrite /WriteSuccessTransactionsBoundary15028.writeSuccessTransactionsMachine15028;
    iFrame;
    try prepare_sidecond;
    try solve_zesu_ld_array_at;
    try bv_solve;
    try iFrame.
  - iFrame.
    rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done.
  Unshelve.
  all: try prepare_sidecond.
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try iFrame.
  all: try done.
  Unshelve.
  all: try exact inhabitant.
  all: try prepare_sidecond.
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try iFrame.
Qed.
