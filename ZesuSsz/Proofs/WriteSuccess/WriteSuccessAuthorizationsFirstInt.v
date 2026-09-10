Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsAuthorizationsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_authorizations_first_int `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x155d8
    (writeSuccessAuthorizationsCopiedSpec AuthorizationsSecondInt P) -∗
  instr_body 0x155cc
    (writeSuccessAuthorizationsCopiedSpec AuthorizationsFirstInt P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hint Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  run_write_success_authorizations_chunk 0x155d8.
  Unshelve. all: try run_write_success_authorizations_return 0x155d8.
  all: try prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  have HscratchStart :
      Z.to_nat (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744)) = 96%nat.
  { replace (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744))%Z with 96%Z
      by lia. reflexivity. }
  have HscratchBounds :
      (Z.to_nat (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744)) + 8 <=
       length current)%nat.
  { rewrite HscratchStart. lia. }
  iRename select
    ((bv_unsigned sp + 1744) ↦ₘ∗
      take
        (Z.to_nat (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744)))
        current)%I into "HscratchPrefix".
  iRename select
    ((bv_unsigned sp + 1744 +
      (Z.to_nat (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744)) + 8)%nat)
      ↦ₘ∗ drop
        (Z.to_nat (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744)) + 8)
        current)%I into "HscratchSuffix".
  iRename select
    ((bv_unsigned sp + 1840) ↦ₘ
      Z_to_bv 64
        (little_endian_to_bv 8
          (take 8
            (drop
              (Z.to_nat
                (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744)))
              current))))%I into "HscratchWord".
  have HscratchWordAddress :
      (bv_unsigned sp + 1744 + Z.of_N (8 `div` 8) *
        Z.of_nat
          (Z.to_nat (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744))))%Z =
      (bv_unsigned sp + 1840)%Z.
  { rewrite HscratchStart.
    change (bv_unsigned sp + 1744 + 1 * 96 = bv_unsigned sp + 1840)%Z.
    lia. }
  have HscratchSuffixAddress :
      (bv_unsigned sp + 1744 +
        (Z.to_nat (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744)) + 8)%nat)%Z =
      (bv_unsigned sp + 1744 +
        Z.of_nat
          (Z.to_nat (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744)) + 8))%Z
      by reflexivity.
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (bv_unsigned sp + 1744)%Z current
    (Z.to_nat (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744)))
    (bv_unsigned sp + 1744 +
      (Z.to_nat (bv_unsigned sp + 1840 - (bv_unsigned sp + 1744)) + 8)%nat)%Z
    (bv_unsigned sp + 1840)%Z with
    "HscratchPrefix HscratchSuffix HscratchWord [] [] []") as "Hcurrent".
  { iPureIntro. exact HscratchSuffixAddress. }
  { iPureIntro. exact (eq_sym HscratchWordAddress). }
  { iPureIntro. exact HscratchBounds. }
  iExists
    (tail, suffix, prefix, prefix ++ suffix, processed,
     (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.
