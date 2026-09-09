From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d20.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessEncoderIntRegs1 regs sp :=
  writeSuccess15d10Regs regs sp.
Definition writeSuccessEncoderIntRegs2 regs sp :=
  writeSuccess15d14Regs (writeSuccessEncoderIntRegs1 regs sp).
Definition writeSuccessEncoderIntRegs3 regs sp :=
  writeSuccess15d18Regs (writeSuccessEncoderIntRegs2 regs sp).
Definition writeSuccessEncoderIntRegs4 regs sp :=
  writeSuccess15d1cRegs (writeSuccessEncoderIntRegs3 regs sp)
    (sp - BV 64 16)%bv.
Definition writeSuccessEncoderIntRegs5 regs sp :=
  writeSuccess15d20Regs (writeSuccessEncoderIntRegs4 regs sp).
Definition writeSuccessEncoderIntRegs6 regs sp :=
  writeSuccess15d24Regs (writeSuccessEncoderIntRegs5 regs sp).
Definition writeSuccessEncoderIntRegs7 regs sp :=
  writeSuccess15d28Regs (writeSuccessEncoderIntRegs6 regs sp).

Definition writeSuccessEncoderIntGlobal1 global sp returnAddress :=
  writeSuccess15d14Global global (sp - BV 64 16)%bv returnAddress.
Definition writeSuccessEncoderIntGlobal2 global sp returnAddress value :=
  writeSuccess15d18Global
    (writeSuccessEncoderIntGlobal1 global sp returnAddress)
    (sp - BV 64 16)%bv value.

Lemma writeSuccessEncoderIntStackExact sp :
  (sp + BV 64 18446744073709551600)%bv = (sp - BV 64 16)%bv.
Proof. bv_solve. Qed.

Lemma writeSuccessEncoderIntRegs7LookupOther regs sp register :
  register <> "PC" -> register <> "x1" -> register <> "x2" ->
  register <> "x10" -> register <> "x11" ->
  writeSuccessEncoderIntRegs7 regs sp !! register = regs !! register.
Proof.
  intros Hpc Hx1 Hx2 Hx10 Hx11.
  unfold writeSuccessEncoderIntRegs7, writeSuccessEncoderIntRegs6,
    writeSuccessEncoderIntRegs5, writeSuccessEncoderIntRegs4,
    writeSuccessEncoderIntRegs3, writeSuccessEncoderIntRegs2,
    writeSuccessEncoderIntRegs1.
  rewrite writeSuccess15d28RegsLookupOther; try assumption.
  rewrite writeSuccess15d24RegsLookupOther; try assumption.
  rewrite writeSuccess15d20RegsLookupOther; try assumption.
  rewrite writeSuccess15d1cRegsLookupOther; try assumption.
  rewrite writeSuccess15d18RegsLookupOther; try assumption.
  rewrite writeSuccess15d14RegsLookupOther; try assumption.
  rewrite writeSuccess15d10RegsLookupOther; try assumption; reflexivity.
Qed.

Lemma writeSuccessEncoderIntRegs7Pc regs sp :
  writeSuccessEncoderIntRegs7 regs sp !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x10190)).
Proof.
  unfold writeSuccessEncoderIntRegs7, writeSuccess15d28Regs.
  rewrite lookup_insert. destruct writeSuccess15d28ValuesExact as (_ & _ & _ & ->).
  reflexivity.
Qed.

Lemma writeSuccessEncoderIntRegs7X1 regs sp :
  writeSuccessEncoderIntRegs7 regs sp !! "x1" =
    Some (RVal_Bits (Z_to_bv 64 0x15d2c)).
Proof.
  unfold writeSuccessEncoderIntRegs7, writeSuccess15d28Regs.
  rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
  destruct writeSuccess15d28ValuesExact as (_ & -> & _). reflexivity.
Qed.

Lemma writeSuccessEncoderIntRegs7X2 regs sp :
  writeSuccessEncoderIntRegs7 regs sp !! "x2" =
    Some (RVal_Bits (sp - BV 64 16)%bv).
Proof.
  unfold writeSuccessEncoderIntRegs7, writeSuccessEncoderIntRegs6,
    writeSuccessEncoderIntRegs5, writeSuccessEncoderIntRegs4,
    writeSuccessEncoderIntRegs3, writeSuccessEncoderIntRegs2,
    writeSuccessEncoderIntRegs1.
  rewrite writeSuccess15d28RegsLookupOther; try discriminate.
  rewrite writeSuccess15d24RegsLookupOther; try discriminate.
  rewrite writeSuccess15d20RegsLookupOther; try discriminate.
  rewrite writeSuccess15d1cRegsLookupOther; try discriminate.
  rewrite writeSuccess15d18RegsLookupOther; try discriminate.
  rewrite writeSuccess15d14RegsLookupOther; try discriminate.
  unfold writeSuccess15d10Regs. rewrite lookup_insert_ne; last discriminate.
  rewrite lookup_insert writeSuccessEncoderIntStackExact. reflexivity.
Qed.

Lemma writeSuccessEncoderIntRegs7X10 regs sp :
  writeSuccessEncoderIntRegs7 regs sp !! "x10" =
    Some (RVal_Bits (sp - BV 64 16)%bv).
Proof.
  unfold writeSuccessEncoderIntRegs7, writeSuccessEncoderIntRegs6,
    writeSuccessEncoderIntRegs5, writeSuccessEncoderIntRegs4.
  rewrite writeSuccess15d28RegsLookupOther; try discriminate.
  rewrite writeSuccess15d24RegsLookupOther; try discriminate.
  rewrite writeSuccess15d20RegsLookupOther; try discriminate.
  unfold writeSuccess15d1cRegs. rewrite lookup_insert_ne; last discriminate.
  rewrite lookup_insert. repeat f_equal. bv_solve.
Qed.

Lemma writeSuccessEncoderIntRegs7X11 regs sp :
  writeSuccessEncoderIntRegs7 regs sp !! "x11" =
    Some (RVal_Bits (BV 64 8)).
Proof.
  unfold writeSuccessEncoderIntRegs7, writeSuccessEncoderIntRegs6,
    writeSuccessEncoderIntRegs5.
  rewrite writeSuccess15d28RegsLookupOther; try discriminate.
  rewrite writeSuccess15d24RegsLookupOther; try discriminate.
  unfold writeSuccess15d20Regs. rewrite lookup_insert_ne; last discriminate.
  rewrite lookup_insert. reflexivity.
Qed.

Lemma writeSuccessEncoderIntForallTwo {A} (P Q R : A -> Prop) items :
  Forall P items -> Forall Q items ->
  (forall item, P item -> Q item -> R item) -> Forall R items.
Proof.
  intros HP HQ Himp. induction HP; inversion HQ; subst; constructor; eauto.
Qed.

Lemma writeSuccessEncoderIntSystemKeys :
  Forall (fun entry =>
    match entry.1 with
    | KindReg register | KindField register _ =>
        register <> "PC" /\ register <> "x1" /\ register <> "x2" /\
        register <> "x10" /\ register <> "x11"
    end) zesu_ram_sys_regs.
Proof. unfold zesu_ram_sys_regs, zesu_sys_regs. repeat constructor; discriminate. Qed.

Lemma writeSuccessEncoderIntUpdateSystemKeys register :
  In register ["PC"; "x1"; "x2"; "x10"; "x11"] ->
  Forall (fun entry =>
    match entry.1 with
    | KindReg systemRegister | KindField systemRegister _ =>
        systemRegister <> register
    end) zesu_ram_sys_regs.
Proof.
  intros Hin.
  pose proof writeSuccessEncoderIntSystemKeys as Hkeys.
  rewrite !Forall_forall in Hkeys |- *.
  intros [[systemRegister|systemRegister field] shape] Hentry;
    specialize (Hkeys _ Hentry); cbn in Hkeys |- *.
  all: cbn in Hin;
    destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; subst register; tauto.
Qed.

Lemma writeSuccessEncoderIntFactsInsert regs register (value : bv 64) :
  In register ["PC"; "x1"; "x2"; "x10"; "x11"] ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (<[register := RVal_Bits value]> regs).
Proof.
  intros Hregister (Hmstatus & Hsys & Hgeneral). repeat split.
  - unfold writeSuccessWithdrawalsOperationalMstatus in Hmstatus |- *.
    cbn in Hmstatus |- *. rewrite lookup_insert_ne; first exact Hmstatus.
    cbn in Hregister. naive_solver.
  - eapply writeSuccessEncoderIntForallTwo;
      [exact Hsys|apply writeSuccessEncoderIntUpdateSystemKeys; exact Hregister|].
    intros [[systemRegister|systemRegister field] shape] Hshape Hdifferent;
      cbn in Hdifferent.
    + unfold writeSuccessWithdrawalsOperationalRegisterShape in Hshape |- *.
      cbn in Hshape |- *. destruct Hshape as (root & Hlookup & Hshape).
      exists root. split; last exact Hshape.
      rewrite lookup_insert_ne; [exact Hlookup|congruence].
    + unfold writeSuccessWithdrawalsOperationalRegisterShape in Hshape |- *.
      cbn in Hshape |- *.
      destruct Hshape as (root & fieldValue & Hlookup & Hread & Hshape).
      exists root, fieldValue. repeat split; try assumption.
      rewrite lookup_insert_ne; [exact Hlookup|congruence].
  - intros queried Hqueried.
    destruct (decide (queried = register)) as [->|Hdifferent].
    + exists value. apply lookup_insert.
    + destruct (Hgeneral queried Hqueried) as (old & Hold).
      exists old. rewrite lookup_insert_ne; [exact Hold|congruence].
Qed.

Lemma writeSuccessEncoderIntRegs7FactsByUpdates regs sp :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessEncoderIntRegs7 regs sp).
Proof.
  intros Hfacts.
  unfold writeSuccessEncoderIntRegs7, writeSuccessEncoderIntRegs6,
    writeSuccessEncoderIntRegs5, writeSuccessEncoderIntRegs4,
    writeSuccessEncoderIntRegs3, writeSuccessEncoderIntRegs2,
    writeSuccessEncoderIntRegs1, writeSuccess15d28Regs,
    writeSuccess15d24Regs, writeSuccess15d20Regs,
    writeSuccess15d1cRegs, writeSuccess15d18Regs,
    writeSuccess15d14Regs, writeSuccess15d10Regs.
  repeat (apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|]).
  exact Hfacts.
Qed.

Lemma writeSuccessEncoderIntRegs7Facts regs sp :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessEncoderIntRegs7 regs sp).
Proof.
  apply writeSuccessEncoderIntRegs7FactsByUpdates.
Qed.

(* The expanded proof remains useful for checking the exact preserved keys. *)
Lemma writeSuccessEncoderIntRegs7FactsExpanded regs sp :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (writeSuccessEncoderIntRegs7 regs sp).
Proof.
  intros (Hmstatus & Hsys & Hgeneral). repeat split.
  - unfold writeSuccessWithdrawalsOperationalMstatus in Hmstatus |- *.
    cbn in Hmstatus |- *. rewrite writeSuccessEncoderIntRegs7LookupOther;
      try discriminate. exact Hmstatus.
  - eapply writeSuccessEncoderIntForallTwo;
      [exact Hsys|apply writeSuccessEncoderIntSystemKeys|].
    intros [[register|register field] shape] Hshape Hkeys; cbn in Hkeys.
    + unfold writeSuccessWithdrawalsOperationalRegisterShape in Hshape |- *.
      cbn in Hshape |- *. destruct Hshape as (root & Hlookup & Hshape).
      exists root. split; last exact Hshape.
      rewrite writeSuccessEncoderIntRegs7LookupOther; first exact Hlookup; tauto.
    + unfold writeSuccessWithdrawalsOperationalRegisterShape in Hshape |- *.
      cbn in Hshape |- *.
      destruct Hshape as (root & value & Hlookup & Hread & Hshape).
      exists root, value. repeat split; try assumption.
      rewrite writeSuccessEncoderIntRegs7LookupOther; first exact Hlookup; tauto.
  - intros register Hin.
    destruct (decide (register = "x1")) as [->|Hx1].
    { exists (Z_to_bv 64 0x15d2c). apply writeSuccessEncoderIntRegs7X1. }
    destruct (decide (register = "x10")) as [->|Hx10].
    { exists (sp - BV 64 16)%bv. apply writeSuccessEncoderIntRegs7X10. }
    destruct (decide (register = "x11")) as [->|Hx11].
    { exists (BV 64 8). apply writeSuccessEncoderIntRegs7X11. }
    destruct (Hgeneral register Hin) as (value & Hvalue).
    exists value. rewrite writeSuccessEncoderIntRegs7LookupOther; try assumption.
    all: intros ->; cbn in Hin; naive_solver.
Qed.

Lemma writeSuccessEncoderIntGlobal2Memory global sp returnAddress value :
  (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem) =
  write_mem_list
    (write_mem_list global.(seq_mem) (Z_to_bv 64 (bv_unsigned sp - 8))
      (bv_to_little_endian 8 8 (bv_unsigned returnAddress)))
    (Z_to_bv 64 (bv_unsigned sp - 16))
    (bv_to_little_endian 8 8 (bv_unsigned value)).
Proof.
  unfold writeSuccessEncoderIntGlobal2, writeSuccessEncoderIntGlobal1,
    writeSuccess15d18Global, writeSuccess15d18Memory,
    writeSuccess15d14Global, writeSuccess15d14Memory,
    writeSuccess15d18Address, writeSuccess15d14Address,
    writeSuccess15d18Bytes, writeSuccess15d14Bytes.
  cbn.
  replace (sp - BV 64 16 + BV 64 8)%bv with
    (Z_to_bv 64 (bv_unsigned sp - 8)) by (apply bv_eq; bv_solve).
  replace (sp - BV 64 16 + BV 64 0)%bv with
    (Z_to_bv 64 (bv_unsigned sp - 16)) by (apply bv_eq; bv_solve).
  reflexivity.
Qed.

Print Assumptions writeSuccessEncoderIntRegs7Facts.
Print Assumptions writeSuccessEncoderIntGlobal2Memory.
