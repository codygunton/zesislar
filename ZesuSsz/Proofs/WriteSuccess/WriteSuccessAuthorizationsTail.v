From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsAuthorizationsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsSpec.

Import ListNotations.
Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_authorizations_tail `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15590 (writeSuccessAuthorizationsLoopSpec P) -∗
  instr_body 0x15614 (writeSuccessAuthorizationsTailSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hloop".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  do 101 liAStep.
  iRename select (base ↦ₘ∗ prefix)%I into "Hprefix".
  iRename select (bv_unsigned pointer ↦ₘ∗ suffix)%I into "Hsuffix".
  iDestruct (mem_mapsto_array_app 8%N (bv_unsigned pointer) (DfracOwn 1)
    (take 144 suffix) (drop 144 suffix) with "[Hsuffix]") as
    "[Hcurrent Hrest]".
  { rewrite take_drop. iExact "Hsuffix". }
  have Htake : length (take 144 suffix) = 144%nat.
  { rewrite length_take. lia. }
  have HpointerPrefix : bv_unsigned pointer =
      (base + Z.of_N (8 `div` 8) * length prefix)%Z.
  { cbn. rewrite H3 H1. nia. }
  iEval (rewrite HpointerPrefix) in "Hcurrent".
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    prefix (take 144 suffix) (length prefix) eq_refl
    with "Hprefix Hcurrent") as "Hprefix".
  iEval (rewrite Htake) in "Hrest".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  - have Hremaining : remaining = 0%nat.
    { bv_simplify_arith H13. bv_solve. }
    subst remaining.
    rewrite take_ge; [done | simpl in H2; lia].
  - have Hremaining : remaining = 0%nat.
    { bv_simplify_arith H13. bv_solve. }
    subst remaining. done.
  - have Hremaining : remaining = 0%nat.
    { bv_simplify_arith H13. bv_solve. }
    subst remaining.
    bv_simplify_arith. rewrite H3. bv_solve.
  - destruct remaining as [|remaining'].
    { exfalso. apply H13. bv_solve. }
    iExists
      (tail, drop 144 suffix, prefix ++ take 144 suffix, prefix ++ suffix,
       remaining', (processed + 1)%nat,
       (processed + S (S remaining'))%nat, base, tt)ₗ.
    liARun.
    Unshelve.
    all: try prepare_sidecond.
    all: try assumption.
    all: try (cbn; rewrite ?length_take ?length_drop; lia).
    all: try rewrite ?take_drop ?app_assoc.
    all: try bv_solve.
    all: try nia.
    all: try iFrame.
    Unshelve.
    all: try (rewrite <- app_assoc, take_drop; done).
    all: try (rewrite length_app H1 Htake; nia).
    remember (drop 144 suffix) as rest eqn:Hrest.
    have HrestLength : length rest = (144 * S remaining')%nat.
    { rewrite Hrest length_drop H2. nia. }
    destruct rest as [|hd tl]; simpl in HrestLength; [lia |].
    eexists hd, tl. split.
    { done. }
    apply Nat.succ_inj.
    change (S (length tl) = 144 * S remaining')%nat.
    exact HrestLength.
Qed.
