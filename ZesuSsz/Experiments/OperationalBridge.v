From iris.program_logic Require Import language.
Require Import isla.riscv64.riscv64.

Record OperationalState : Type := {
  operationalLocal : seq_local_state;
  operationalGlobal : seq_global_state
}.

Definition operationalPc (state : OperationalState) : option Z :=
  match operationalLocal state with
  | {| seq_regs := regs; seq_pc_reg := pcReg |} =>
      match regs !! pcReg with
      | Some (RVal_Bits pc) =>
          if N.eqb (bvn_n pc) 64 then Some (bvn_unsigned pc) else None
      | _ => None
      end
  end.

(** One contract step executes one instruction trace from [tnil] to [tnil]. *)
Definition operationalInstructionStep (_ : nat)
    (before after : OperationalState) : Prop :=
  exists (pc : bv 64) trace observations,
    seq_trace (operationalLocal before) = tnil /\
    seq_nb_state (operationalLocal before) = false /\
    seq_regs (operationalLocal before) !!
      seq_pc_reg (operationalLocal before) = Some (RVal_Bits pc) /\
    seq_instrs (operationalGlobal before) !! pc = Some trace /\
    nsteps (S (isla_trace_length trace))
      ([operationalLocal before], operationalGlobal before)
      observations
      ([operationalLocal after], operationalGlobal after) /\
    seq_trace (operationalLocal after) = tnil /\
    seq_nb_state (operationalLocal after) = false.

Definition operationalLocalState (regs : reg_map) : seq_local_state := {|
  seq_trace := tnil;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition operationalGlobalState
    (instructions : gmap (bv 64) isla_trace) (memory : mem_map) :
    seq_global_state := {|
  seq_instrs := instructions;
  seq_mem := memory
|}.

Definition operationalState (instructions : gmap (bv 64) isla_trace)
    (regs : reg_map) (memory : mem_map) : OperationalState := {|
  operationalLocal := operationalLocalState regs;
  operationalGlobal := operationalGlobalState instructions memory
|}.

(** Bit-vector helpers used by generated instruction traces. *)
Lemma readAccessorZToBv n z `{!BvWf n z} :
  read_accessor [] (RVal_Bits (Z_to_bv n z)) =
    Some (RVal_Bits (BV n z)).
Proof.
  cbn. f_equal. f_equal. f_equal.
  apply bvn_eq. split; first reflexivity.
  unfold bvn_unsigned. cbn.
  rewrite Z_to_bv_unsigned bv_unsigned_BV.
  apply bv_wrap_small. apply bv_wf_in_range. exact BvWf0.
Qed.

Lemma bvExtractLowThreeZero (value : bv 64) :
  bv_unsigned value `mod` 8 = 0 -> bv_extract 0 3 value = 0%bv.
Proof.
  intros Haligned. apply bv_eq.
  rewrite bv_extract_0_unsigned.
  unfold bv_wrap. cbn. exact Haligned.
Qed.

Ltac operational_pure_match :=
  cbn;
  repeat first [left | split | eexists];
  try reflexivity.

Lemma nstepsSeqStep n local global local' global' final :
  seq_step local global [] local' global' [] ->
  nsteps n ([local'], global') [] final ->
  nsteps (S n) ([local], global) [] final.
Proof.
  intros Hstep Hsteps.
  eapply nsteps_l with
    (ρ2 := ([local'], global')) (κ := []) (κs := []).
  - eapply step_atomic with (t1 := []) (t2 := []) (efs := []).
    + reflexivity.
    + reflexivity.
    + exact Hstep.
  - exact Hsteps.
Qed.

Ltac operational_trace_step_visible :=
  eapply nstepsSeqStep;
  [ eapply SeqStep with (κ' := None);
    [ reflexivity |
      first [eapply DeclareConstBitVecS' |
             econstructor; cbn; reflexivity |
             constructor] |
      operational_pure_match ] |
    cbn ].

Ltac operational_trace_step :=
  eapply nsteps_l with (κ := []) (κs := []);
  [ eapply step_atomic with (t1 := []) (t2 := []) (efs := []);
    [ reflexivity | reflexivity |
      eapply SeqStep with (κ' := None);
      [ reflexivity |
        first [eapply DeclareConstBitVecS' |
               econstructor; cbn; reflexivity |
               constructor] |
        operational_pure_match ] ] |
    cbn ].

(** Start one instruction and leave only its trace events as proof goals. *)
Ltac operational_begin_instruction pc trace :=
  unfold operationalInstructionStep;
  eexists pc, trace, [];
  repeat split; try reflexivity; try assumption;
  cbn;
  eapply nsteps_l with (κ := []) (κs := []);
  [ eapply step_atomic with (t1 := []) (t2 := []) (efs := []);
    [ reflexivity | reflexivity |
      eapply SeqStep with (κ' := None);
      [ reflexivity | constructor |
        cbn; split; [reflexivity|];
        eexists pc; split; [first [reflexivity | assumption]|];
        cbn; repeat split; reflexivity ] ] |
    cbn ].
