From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1501c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15028.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_1501c_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

Ltac solve_write_success_1501c_wave :=
  try prepare_sidecond;
  try assumption;
  try (cbn; rewrite ?length_take ?length_drop; lia);
  try solve_zesu_ld_array_at;
  try bv_solve;
  try lia;
  try iFrame;
  try exact inhabitant;
  try (repeat iIntros "?"; liARun).

Ltac recombine_write_success_transactions_three_u64
    pointer currentAddress current Hunsigned :=
  let Hstart0 := fresh "Hstart0" in
  have Hstart0 :
      Z.to_nat (currentAddress + 48 - currentAddress) = 48%nat;
  [ replace (currentAddress + 48 - currentAddress)%Z with 48%Z by lia;
    reflexivity
  | ];
  let Hstart1 := fresh "Hstart1" in
  have Hstart1 :
      Z.to_nat
        (currentAddress + 56 -
         (currentAddress + (48 + 8)%nat)) = 0%nat;
  [ replace
      (currentAddress + 56 -
       (currentAddress + (48 + 8)%nat))%Z with 0%Z by lia;
    reflexivity
  | ];
  let Hstart2 := fresh "Hstart2" in
  have Hstart2 :
      Z.to_nat
        (currentAddress + 64 -
         (currentAddress + (48 + 8)%nat + (0 + 8)%nat)) = 0%nat;
  [ replace
      (currentAddress + 64 -
       (currentAddress + (48 + 8)%nat + (0 + 8)%nat))%Z
      with 0%Z by lia;
    reflexivity
  | ];
  let Haddress1 := fresh "Haddress1" in
  have Haddress1 :
      (currentAddress + (48 + 8)%nat)%Z = currentAddress + 56;
  [ lia | ];
  let Haddress2 := fresh "Haddress2" in
  have Haddress2 :
      (currentAddress + (48 + 8)%nat + (0 + 8)%nat)%Z =
      currentAddress + 64;
  [ lia | ];
  let Haddress3 := fresh "Haddress3" in
  have Haddress3 :
      (currentAddress + (48 + 8)%nat + (0 + 8)%nat + (0 + 8)%nat)%Z =
      currentAddress + 72;
  [ lia | ];
  iRename select (_ ↦ₘ∗ take _ current)%I into "Hprefix0";
  iRename select ((currentAddress + 48) ↦ₘ _)%I into "Hword0";
  iRename select
    (_ ↦ₘ∗ take _ (drop _ current))%I
    into "Hprefix1";
  iRename select ((currentAddress + 56) ↦ₘ _)%I into "Hword1";
  iRename select
    (_ ↦ₘ∗ take _ (drop _ (drop _ current)))%I
    into "Hprefix2";
  iRename select ((currentAddress + 64) ↦ₘ _)%I into "Hword2";
  iRename select
    (_ ↦ₘ∗ drop _ (drop _ (drop _ current)))%I
    into "Hsuffix3";
  iEval (rewrite Hstart0; cbn) in "Hprefix0";
  iEval (rewrite Hstart0; cbn) in "Hword0";
  iEval (rewrite Hstart0 Hstart1 Haddress1; cbn) in "Hprefix1";
  iEval (rewrite Hstart0 Hstart1; cbn) in "Hword1";
  iEval (rewrite Hstart0 Hstart1 Hstart2 Haddress2; cbn) in "Hprefix2";
  iEval (rewrite Hstart0 Hstart1 Hstart2; cbn) in "Hword2";
  iEval (rewrite Hstart0 Hstart1 Hstart2 Haddress3; cbn) in "Hsuffix3";
  iPoseProof (write_success_recombine_three_u64 currentAddress current with
    "Hprefix0 Hword0 Hprefix1 Hword1 Hprefix2 Hword2 Hsuffix3 []")
    as "Hcurrent";
  [ iPureIntro; lia | ];
  iRename select ("x18" ↦ᵣ RVal_Bits _)%I into "Hx18Loaded";
  iRename select ("x20" ↦ᵣ RVal_Bits _)%I into "Hx20Loaded";
  iRename select ("x29" ↦ᵣ RVal_Bits _)%I into "Hx29Loaded";
  iEval (rewrite Hstart0; cbn) in "Hx18Loaded";
  iEval (rewrite Hstart0 Hstart1; cbn) in "Hx20Loaded";
  iEval (rewrite Hstart0 Hstart1 Hstart2 !drop_drop; cbn) in "Hx29Loaded".

Lemma write_success_transactions_chunk_1501c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15028 (writeSuccessTransactionsAt15028Spec P) -∗
  instr_body 0x1501c (writeSuccessTransactionsAt1501cSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve. all: solve_write_success_1501c_wave.
  Unshelve. all: solve_write_success_1501c_wave.
  Unshelve. all: solve_write_success_1501c_wave.
  Unshelve. all: solve_write_success_1501c_wave.
  Unshelve.
  all: try (rewrite !write_success_1501c_current_unsigned; try lia).
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  have Hunsigned :
      bv_unsigned (Z_to_bv 64 (base + 288 * length processed)) =
      base + 288 * length processed.
  { apply write_success_1501c_current_unsigned; lia. }
  recombine_write_success_transactions_three_u64
    (Z_to_bv 64 (base + 288 * length processed))
    (base + 288 * length processed)
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    Hunsigned.
  iRename select
    ((reg_col zesu_ram_sys_regs ∗
      "x10" ↦ᵣ RVal_Bits
        (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
      "x18" ↦ᵣ RVal_Bits _ ∗ "x20" ↦ᵣ RVal_Bits _ ∗
      "x29" ↦ᵣ RVal_Bits _ -∗
      writeSuccessTransactionsMachine15028
        sp base transactions processed transaction))%I into "HmachineWand".
  iRename select (reg_col zesu_ram_sys_regs)%I into "Hsys".
  iRename select
    ("x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))))%I
    into "Hx10".
  iPoseProof ("HmachineWand" with
    "[$Hsys $Hx10 $Hx18Loaded $Hx20Loaded $Hx29Loaded]") as "Hmachine".
  iExists (tail, suffix, prefix, bytes, remaining, processed, transactions,
    transaction, base, sp, tt)ₗ.
  iFrame.
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.
