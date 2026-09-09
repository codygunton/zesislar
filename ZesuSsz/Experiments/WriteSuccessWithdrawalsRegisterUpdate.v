From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.

Import ListNotations.

Definition writeSuccessWithdrawalsGeneralRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x10"; "x11";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x19"; "x20";
   "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"; "x28";
   "x29"; "x30"; "x31"].

Definition writeSuccessRegisterKindName (kind : reg_kind) : string :=
  match kind with
  | KindReg register => register
  | KindField register _ => register
  end.

Lemma writeSuccessOperationalRegisterFactsInsertBit regs register (value : bv 64) :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  register <> "mstatus" ->
  Forall (fun entry => writeSuccessRegisterKindName entry.1 <> register)
    zesu_ram_sys_regs ->
  (register = "PC" \/ In register writeSuccessWithdrawalsGeneralRegisters) ->
  writeSuccessWithdrawalsOperationalRegisterFacts
    (<[register := RVal_Bits value]> regs).
Proof.
  intros (Hmstatus & Hsystem & Hgeneral) HmstatusName HsystemNames Hregister.
  split.
  - unfold writeSuccessWithdrawalsOperationalMstatus in Hmstatus |- *.
    cbn in Hmstatus |- *. rewrite lookup_insert_ne; assumption.
  - split.
    + revert HsystemNames. induction Hsystem as [|[kind shape] entries Hentry Hentries IH];
        intros Hnames; first constructor.
      apply Forall_cons_iff in Hnames as [Hname Hnames]. constructor.
      * destruct kind as [root|root field]; cbn in *.
        -- destruct Hentry as (old & Hlookup & Hshape).
           exists old. split; last exact Hshape.
           rewrite lookup_insert_ne; [exact Hlookup | congruence].
        -- destruct Hentry as (old & selected & Hlookup & Hread & Hshape).
           exists old, selected. repeat split; try assumption.
           rewrite lookup_insert_ne; [exact Hlookup | congruence].
      * apply IH. exact Hnames.
    + intros target Hin.
      destruct (decide (target = register)) as [->|Hne].
      * exists value. apply lookup_insert.
      * rewrite lookup_insert_ne; last congruence.
        apply Hgeneral. exact Hin.
Qed.

Lemma writeSuccessWithdrawalsRegisterFrameInsertBit regs frame register
    (value : bv 64) :
  writeSuccessWithdrawalsRegisterFrame regs frame ->
  ~ In register writeSuccessWithdrawalsProtectedRegisters ->
  writeSuccessWithdrawalsRegisterFrame
    (<[register := RVal_Bits value]> regs) frame.
Proof.
  unfold writeSuccessWithdrawalsRegisterFrame.
  intros Hframe Houtside.
  apply Forall_forall. intros target Hin.
  rewrite lookup_insert_ne.
  - apply (proj1 (Forall_forall _ _) Hframe). exact Hin.
  - intros ->. apply Houtside. apply elem_of_list_In. exact Hin.
Qed.

Print Assumptions writeSuccessOperationalRegisterFactsInsertBit.
Print Assumptions writeSuccessWithdrawalsRegisterFrameInsertBit.
