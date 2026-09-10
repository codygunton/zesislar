Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsAuthorizationsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_authorizations_second_u256 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  instr_body 0x155fc
    (writeSuccessAuthorizationsCopiedSpec AuthorizationsThirdU256 P) -∗
  instr_body 0x155e4
    (writeSuccessAuthorizationsCopiedSpec AuthorizationsSecondU256 P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hu256 Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  run_write_success_authorizations_chunk 0x155fc.
  Unshelve. all: try run_write_success_authorizations_return 0x155fc.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  iExists
    (tail, suffix, prefix, prefix ++ suffix, processed,
     (processed + S remaining)%nat, base, tt)ₗ.
  iRename select
    ((bv_unsigned sp + 1744) ↦ₘ∗
      take (Z.to_nat (bv_unsigned sp + 1776 - (bv_unsigned sp + 1744)))
        current)%I into "Hprefix32".
  iAssert (writeSuccessAuthorizationsHeld
    ((bv_unsigned sp + 1744) ↦ₘ∗
      take (Z.to_nat (bv_unsigned sp + 1776 - (bv_unsigned sp + 1744)))
        current))%I
    with "[Hprefix32]" as "HheldPrefix".
  { rewrite /writeSuccessAuthorizationsHeld. iExact "Hprefix32". }
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try liAStep.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  iEval (unfold writeSuccessAuthorizationsHeld) in "HheldPrefix".
  have HscratchStart0 :
      Z.to_nat (bv_unsigned sp + 1776 - (bv_unsigned sp + 1744)) = 32%nat.
  { replace (bv_unsigned sp + 1776 - (bv_unsigned sp + 1744))%Z with 32%Z
      by lia. reflexivity. }
  have HscratchStart1 :
      Z.to_nat
        (bv_unsigned sp + 1784 -
         (bv_unsigned sp + 1744 + (32 + 8)%nat)) = 0%nat.
  { replace
      (bv_unsigned sp + 1784 -
       (bv_unsigned sp + 1744 + (32 + 8)%nat))%Z with 0%Z by lia.
    reflexivity. }
  have HscratchStart2 :
      Z.to_nat
        (bv_unsigned sp + 1792 -
         (bv_unsigned sp + 1744 + (32 + 8)%nat + (0 + 8)%nat)) = 0%nat.
  { replace
      (bv_unsigned sp + 1792 -
       (bv_unsigned sp + 1744 + (32 + 8)%nat + (0 + 8)%nat))%Z with 0%Z
      by lia. reflexivity. }
  have HscratchStart3 :
      Z.to_nat
        (bv_unsigned sp + 1800 -
         (bv_unsigned sp + 1744 + (32 + 8)%nat + (0 + 8)%nat +
          (0 + 8)%nat)) = 0%nat.
  { replace
      (bv_unsigned sp + 1800 -
       (bv_unsigned sp + 1744 + (32 + 8)%nat + (0 + 8)%nat +
        (0 + 8)%nat))%Z with 0%Z by lia.
    reflexivity. }
  iRename select ((bv_unsigned sp + 1776) ↦ₘ _)%I into "Hword0".
  iRename select ((bv_unsigned sp + 1784) ↦ₘ _)%I into "Hword1".
  iRename select ((bv_unsigned sp + 1792) ↦ₘ _)%I into "Hword2".
  iRename select ((bv_unsigned sp + 1800) ↦ₘ _)%I into "Hword3".
  iRename select
    (_ ↦ₘ∗ drop _ (drop _ (drop _ (drop _ current))))%I
    into "HscratchSuffix".
  iEval (rewrite HscratchStart0) in "HheldPrefix".
  iEval (rewrite ?HscratchStart0 ?HscratchStart1) in "Hword1".
  iEval (rewrite ?HscratchStart0 ?HscratchStart1 ?HscratchStart2)
    in "Hword2".
  iEval (rewrite ?HscratchStart0 ?HscratchStart1 ?HscratchStart2
    ?HscratchStart3) in "Hword3".
  iEval (rewrite ?HscratchStart0 ?HscratchStart1 ?HscratchStart2
    ?HscratchStart3) in "HscratchSuffix".
  iPoseProof (write_success_prepend_loaded_u64 _ _ _ _ with
    "Hword3 HscratchSuffix [] []") as "Htail3".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. rewrite ?length_take ?length_drop. lia. }
  iPoseProof (write_success_prepend_loaded_u64 _ _ _ _ with
    "Hword2 Htail3 [] []") as "Htail2".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. rewrite ?length_take ?length_drop. lia. }
  iPoseProof (write_success_prepend_loaded_u64 _ _ _ _ with
    "Hword1 Htail2 [] []") as "Htail1".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. rewrite ?length_take ?length_drop. lia. }
  iEval (rewrite ?HscratchStart0) in "Hword0".
  iPoseProof (write_success_prepend_loaded_u64 _ _ _ _ with
    "Hword0 Htail1 [] []") as "Hregion".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. rewrite ?length_take ?length_drop. lia. }
  iPoseProof (write_success_combine_byte_arrays _ _ _ _ with
    "HheldPrefix Hregion []") as "Hcurrent".
  { iPureIntro. cbn. rewrite ?length_take ?length_drop. lia. }
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try (rewrite !app_length !length_take !length_drop H0; cbn; lia).
  all: lazymatch goal with
    | |- ∃ hd tl, _ = hd :: tl ∧ length tl = 143%nat =>
        destruct current as [|hd rest];
        [cbn in H0; lia |
         cbn; exists hd; eexists; split; [reflexivity |];
         cbn in H0; rewrite !app_length !length_take !length_drop; cbn; lia]
    | _ => idtac
    end.
Qed.
