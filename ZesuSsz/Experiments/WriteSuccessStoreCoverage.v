From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.

Open Scope Z_scope.

Lemma writeSuccessWriteMemMmioOutcomeCovered local global labels
    afterLocal afterGlobal spawned trace' result kind (address : bv 64)
    len tag (value : bv (8 * len)) :
  local.(seq_trace) =
    WriteMem result kind (RVal_Bits (bv_to_bvn address))
      (RVal_Bits (bv_to_bvn value)) len tag Mk_annot :t: trace' ->
  (0 < Z.of_N len)%Z ->
  read_mem global.(seq_mem) (bv_unsigned address) len = None ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  (bv_unsigned address + Z.of_N len <= 2 ^ 64)%Z /\
  set_Forall
    (fun item => ~ (bv_unsigned address <= bv_unsigned item <
      bv_unsigned address + Z.of_N len)%Z) (dom global.(seq_mem)) /\
  labels = [SWriteMem address (bv_to_bvn value)] /\
  afterLocal = local <| seq_trace := trace' |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Hlen Hread Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem.
  destruct Hsem as (memory' & actualAddress & actualValue & Hsem).
  destruct Hsem as (Haddress & Hvalue & Hlen' & Hbranch).
  apply writeSuccessBitsValInjective in Haddress. subst actualAddress.
  apply writeSuccessBitsValInjective in Hvalue. subst actualValue.
  rewrite Hread in Hbranch.
  destruct Hbranch as (Hrange & Houtside & -> & -> & ->).
  repeat split; assumption || reflexivity.
Qed.

Print Assumptions writeSuccessWriteMemMmioOutcomeCovered.
