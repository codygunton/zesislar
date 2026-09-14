Require Import ZesuSsz.Automation.All.
Require Import isla.opsem.

(** A prefix contains only steps inside one instruction trace.  In
    particular it cannot fetch another instruction or abandon a read. *)
Inductive InstructionPrefix : nat -> seq_local_state -> seq_global_state ->
    list seq_label -> seq_local_state -> seq_global_state -> Prop :=
| InstructionPrefixRefl theta sigma :
    InstructionPrefix 0 theta sigma [] theta sigma
| InstructionPrefixStep n theta sigma labels theta' sigma' tail theta'' sigma'' :
    theta.(seq_trace) <> tnil ->
    seq_step theta sigma labels theta' sigma' [] ->
    theta'.(seq_nb_state) = false ->
    InstructionPrefix n theta' sigma' tail theta'' sigma'' ->
    InstructionPrefix (S n) theta sigma (labels ++ tail) theta'' sigma''.

(** Completion includes the Done event.  Its final state either contains
    the next pinned trace or traps because the instruction table has no
    successor.  Both cases use the unchanged seq_step relation. *)
Definition CompletedInstructionSegment theta sigma labels theta' sigma' : Prop :=
  exists n boundary memory prefix last,
    InstructionPrefix n theta sigma prefix boundary memory /\
    boundary.(seq_trace) = tnil /\
    seq_step boundary memory last theta' sigma' [] /\
    labels = prefix ++ last.

Lemma instruction_prefix_append n theta sigma prefix boundary memory
    m tail theta' sigma' :
  InstructionPrefix n theta sigma prefix boundary memory ->
  InstructionPrefix m boundary memory tail theta' sigma' ->
  InstructionPrefix (n + m) theta sigma (prefix ++ tail) theta' sigma'.
Proof.
  intros Hprefix Htail. induction Hprefix.
  - exact Htail.
  - simpl. rewrite <- app_assoc. econstructor; eauto.
Qed.

Lemma instruction_prefix_completed n theta sigma prefix boundary memory
    tail theta' sigma' :
  InstructionPrefix n theta sigma prefix boundary memory ->
  CompletedInstructionSegment boundary memory tail theta' sigma' ->
  CompletedInstructionSegment theta sigma (prefix ++ tail) theta' sigma'.
Proof.
  intros Hprefix [m [done [mem [body [last [Hbody [Hdone [Hstep ->]]]]]]]].
  exists (n + m)%nat, done, mem, (prefix ++ body), last.
  split; [eapply instruction_prefix_append; eauto|].
  repeat split; auto. apply app_assoc.
Qed.

Definition instruction_boundary (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Lemma executor_seq_step theta sigma labels theta' sigma' :
  seq_step theta sigma labels theta' sigma' [] ->
  @step isla_lang ([theta], sigma) labels ([theta'], sigma').
Proof.
  intros Hstep.
  eapply step_atomic with (t1 := []) (t2 := []) (efs := []);
    [reflexivity|reflexivity|exact Hstep].
Qed.

Lemma instruction_prefix_nsteps n theta sigma labels theta' sigma' :
  InstructionPrefix n theta sigma labels theta' sigma' ->
  @nsteps isla_lang n ([theta], sigma) labels ([theta'], sigma').
Proof.
  induction 1.
  - constructor.
  - econstructor; [apply executor_seq_step; eassumption|eassumption].
Qed.

Lemma instruction_prefix_finish n theta sigma prefix boundary memory
    last theta' sigma' :
  InstructionPrefix n theta sigma prefix boundary memory ->
  seq_step boundary memory last theta' sigma' [] ->
  @nsteps isla_lang (S n) ([theta], sigma) (prefix ++ last) ([theta'], sigma').
Proof.
  intros Hprefix Hstep. induction Hprefix.
  - simpl. replace last with (last ++ []) by apply app_nil_r.
    econstructor; [apply executor_seq_step; exact Hstep|constructor].
  - rewrite <- app_assoc.
    econstructor; [apply executor_seq_step; eassumption|apply IHHprefix; exact Hstep].
Qed.

Lemma completed_instruction_nsteps theta sigma labels theta' sigma' :
  CompletedInstructionSegment theta sigma labels theta' sigma' ->
  exists n, @nsteps isla_lang n ([theta], sigma) labels ([theta'], sigma').
Proof.
  intros [n [boundary [memory [prefix [last [Hprefix [_ [Hstep ->]]]]]]]].
  exists (S n). eapply instruction_prefix_finish; eauto.
Qed.

Lemma executor_nsteps_append n (start boundary finish : cfg isla_lang) prefix
    m tail :
  @nsteps isla_lang n start prefix boundary ->
  @nsteps isla_lang m boundary tail finish ->
  @nsteps isla_lang (n + m) start (prefix ++ tail) finish.
Proof.
  intros Hprefix Htail. induction Hprefix.
  - exact Htail.
  - simpl. rewrite <- app_assoc. econstructor; eauto.
Qed.

Inductive CompletedInstructionRun : nat -> seq_local_state -> seq_global_state ->
    list seq_label -> seq_local_state -> seq_global_state -> Prop :=
| CompletedInstructionRunRefl theta sigma :
    CompletedInstructionRun 0 theta sigma [] theta sigma
| CompletedInstructionRunStep n theta sigma prefix boundary memory tail theta' sigma' :
    CompletedInstructionSegment theta sigma prefix boundary memory ->
    CompletedInstructionRun n boundary memory tail theta' sigma' ->
    CompletedInstructionRun (S n) theta sigma (prefix ++ tail) theta' sigma'.

Lemma completed_run_append n theta sigma prefix boundary memory
    m tail theta' sigma' :
  CompletedInstructionRun n theta sigma prefix boundary memory ->
  CompletedInstructionRun m boundary memory tail theta' sigma' ->
  CompletedInstructionRun (n + m) theta sigma (prefix ++ tail) theta' sigma'.
Proof.
  intros Hprefix Htail. induction Hprefix.
  - exact Htail.
  - simpl. rewrite <- app_assoc. econstructor; eauto.
Qed.

Lemma completed_run_nsteps instructions theta sigma labels theta' sigma' :
  CompletedInstructionRun instructions theta sigma labels theta' sigma' ->
  exists steps, @nsteps isla_lang steps ([theta], sigma) labels ([theta'], sigma').
Proof.
  induction 1.
  - exists 0%nat. constructor.
  - destruct (completed_instruction_nsteps _ _ _ _ _ H) as [first Hfirst].
    destruct IHCompletedInstructionRun as [rest Hrest].
    exists (first + rest)%nat. eapply executor_nsteps_append; eauto.
Qed.

Lemma executor_declare_bits n (value : bv n) x ann trace regs sigma :
  seq_step
    (instruction_boundary (Smt (DeclareConst x (Ty_BitVec n)) ann :t: trace) regs)
    sigma [] (instruction_boundary (subst_trace (Val_Bits value) x trace) regs)
    sigma [].
Proof.
  eapply SeqStep with (κ := None) (κ' := None).
  - reflexivity.
  - apply DeclareConstBitVecS'.
  - repeat split; reflexivity.
Qed.

Lemma executor_declare_bool value x ann trace regs sigma :
  seq_step
    (instruction_boundary (Smt (DeclareConst x Ty_Bool) ann :t: trace) regs)
    sigma [] (instruction_boundary (subst_trace (Val_Bool value) x trace) regs)
    sigma [].
Proof.
  eapply SeqStep with (κ := None) (κ' := None).
  - reflexivity.
  - apply DeclareConstBoolS.
  - repeat split; reflexivity.
Qed.

Lemma executor_declare_enum value name x ann trace regs sigma :
  seq_step
    (instruction_boundary (Smt (DeclareConst x (Ty_Enum name)) ann :t: trace) regs)
    sigma [] (instruction_boundary (subst_trace (Val_Enum value) x trace) regs)
    sigma [].
Proof.
  eapply SeqStep with (κ := None) (κ' := None).
  - reflexivity.
  - apply DeclareConstEnumS.
  - repeat split; reflexivity.
Qed.

(** The declaration witness comes from a later read.  Struct fields match
    by position and name. *)
Fixpoint read_symbol (x : var_name) (pattern actual : valu) : option base_val :=
  match pattern with
  | RegVal_Base (Val_Symbolic y) =>
      if bool_decide (x = y) then
        match actual with RegVal_Base value => Some value | _ => None end
      else None
  | RegVal_Struct fields =>
      match actual with
      | RegVal_Struct actual_fields =>
          let fix go fields actual_fields :=
            match fields, actual_fields with
            | (name, value) :: rest, (actual_name, actual_value) :: actual_rest =>
                if String.eqb name actual_name then
                  match read_symbol x value actual_value with
                  | Some result => Some result
                  | None => go rest actual_rest
                  end
                else None
            | _, _ => None
            end in go fields actual_fields
      | _ => None
      end
  | _ => None
  end.

Fixpoint declaration_read (fuel : nat) (x : var_name) (trace : isla_trace)
    (regs : reg_map) (sigma : seq_global_state) : option base_val :=
  match fuel with
  | O => None
  | S fuel' =>
      match trace with
      | ReadReg name al pattern _ :t: rest =>
          match regs !! name with
          | Some actual =>
              match read_accessor al pattern, read_accessor al actual with
              | Some pattern', Some actual' =>
                  match read_symbol x pattern' actual' with
                  | Some result => Some result
                  | None => declaration_read fuel' x rest regs sigma
                  end
              | _, _ => None
              end
          | None => None
          end
      | ReadMem (RegVal_Base (Val_Symbolic y)) _ (RVal_Bits address) len _ _ :t: rest =>
          if bool_decide (x = y) then
            address' ← bvn_to_bv 64 address;
            value ← read_mem sigma.(seq_mem) (bv_unsigned address') len;
            Some (Val_Bits value)
          else declaration_read fuel' x rest regs sigma
      | WriteReg _ _ _ _ :t: _ => None
      | _ :t: rest => declaration_read fuel' x rest regs sigma
      | _ => None
      end
  end.

Lemma read_symbol_base x value :
  read_symbol x (RegVal_Base (Val_Symbolic x)) (RegVal_Base value) = Some value.
Proof. simpl. rewrite bool_decide_true; done. Qed.

Definition ExecutorResult :=
  (reg_map * seq_global_state * list seq_label * list Prop)%type.

(** Register events do not change memory or emit observable labels. *)
Definition exec_register_event (e : event) (regs : reg_map)
    (sigma : seq_global_state) : option ExecutorResult :=
  match e with
  | ReadReg name al pattern _ =>
      actual ← regs !! name;
      value ← read_accessor al actual;
      pattern' ← read_accessor al pattern;
      Some (regs, sigma, [], [pattern' = value])
  | AssumeReg name al value _ =>
      actual ← regs !! name;
      Some (regs, sigma, [], [read_accessor al actual = Some value])
  | WriteReg name al pattern _ =>
      actual ← regs !! name;
      value ← read_accessor al pattern;
      result ← write_accessor al actual value;
      Some (<[name := result]> regs, sigma, [], [])
  | _ => None
  end.

Definition ExecutorConditions (conditions : list Prop) : Prop :=
  Forall (fun condition => condition) conditions.

Lemma exec_register_read name al pattern ann regs sigma regs' sigma' labels conditions
    trace :
  exec_register_event (ReadReg name al pattern ann) regs sigma =
    Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions ->
  seq_step (instruction_boundary (ReadReg name al pattern ann :t: trace) regs)
    sigma labels (instruction_boundary trace regs') sigma' [].
Proof.
  unfold exec_register_event.
  destruct (regs !! name) as [actual|] eqn:Hreg; simpl; [|discriminate].
  destruct (read_accessor al actual) as [value|] eqn:Hactual; simpl; [|discriminate].
  destruct (read_accessor al pattern) as [value'|] eqn:Hpattern; simpl; [|discriminate].
  intros Heq Hconditions. inversion Heq; subst; clear Heq.
  inversion Hconditions; subst.
  eapply SeqStep with (κ := Some (LReadReg name al pattern)) (κ' := None).
  - reflexivity.
  - constructor.
  - exists actual, value, value. repeat split; auto.
Qed.

Lemma exec_register_assume name al value ann regs sigma regs' sigma' labels conditions
    trace :
  exec_register_event (AssumeReg name al value ann) regs sigma =
    Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions ->
  seq_step (instruction_boundary (AssumeReg name al value ann :t: trace) regs)
    sigma labels (instruction_boundary trace regs') sigma' [].
Proof.
  unfold exec_register_event.
  destruct (regs !! name) as [actual|] eqn:Hreg; simpl; [|discriminate].
  intros Heq Hconditions. inversion Heq; subst; clear Heq.
  inversion Hconditions; subst.
  eapply SeqStep with (κ := Some (LAssumeReg name al value)) (κ' := None).
  - reflexivity.
  - constructor.
  - exists actual. repeat split; auto.
Qed.

Lemma exec_register_write name al pattern ann regs sigma regs' sigma' labels conditions
    trace :
  exec_register_event (WriteReg name al pattern ann) regs sigma =
    Some (regs', sigma', labels, conditions) ->
  seq_step (instruction_boundary (WriteReg name al pattern ann :t: trace) regs)
    sigma labels (instruction_boundary trace regs') sigma' [].
Proof.
  unfold exec_register_event.
  destruct (regs !! name) as [actual|] eqn:Hreg; simpl; [|discriminate].
  destruct (read_accessor al pattern) as [value|] eqn:Hpattern; simpl; [|discriminate].
  destruct (write_accessor al actual value) as [result|] eqn:Hwrite; simpl; [|discriminate].
  intros Heq. inversion Heq; subst; clear Heq.
  eapply SeqStep with (κ := Some (LWriteReg name al pattern)) (κ' := None).
  - reflexivity.
  - constructor.
  - exists actual, result, value. repeat split; auto.
Qed.

Lemma exec_register_event_sound e regs sigma regs' sigma' labels conditions trace :
  exec_register_event e regs sigma = Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions ->
  seq_step (instruction_boundary (e :t: trace) regs)
    sigma labels (instruction_boundary trace regs') sigma' [].
Proof.
  destruct e; simpl; try discriminate.
  - eapply exec_register_read.
  - intros Hresult _. eapply exec_register_write; exact Hresult.
  - eapply exec_register_assume.
Qed.

Definition exec_memory_event (e : event) (regs : reg_map)
    (sigma : seq_global_state) : option ExecutorResult :=
  match e with
  | ReadMem data kind (RVal_Bits address) len tag _ =>
      match data with
      | RVal_Bits value =>
          let address' := Z_to_bv 64 (bvn_unsigned address) in
          let value' := Z_to_bv (8 * len) (bvn_unsigned value) in
          match read_mem sigma.(seq_mem) (bv_unsigned address') len with
          | Some memory =>
              Some (regs, sigma, [],
                [RVal_Bits address = RVal_Bits address';
                 data = RVal_Bits value'; 0 < Z.of_N len;
                 memory = bv_to_bvn value'])
          | None => None
          end
      | _ => None
      end
  | WriteMem result kind (RVal_Bits address) data len tag _ =>
      match data with
      | RVal_Bits value =>
          let address' := Z_to_bv 64 (bvn_unsigned address) in
          let value' := Z_to_bv (8 * len) (bvn_unsigned value) in
          let conditions :=
            [RVal_Bits address = RVal_Bits address';
             data = RVal_Bits value'; 0 < Z.of_N len] in
          match read_mem sigma.(seq_mem) (bv_unsigned address') len with
          | Some _ =>
              Some (regs,
                sigma <| seq_mem := write_mem len sigma.(seq_mem) address'
                  (bv_unsigned value') |>, [], conditions)
          | None =>
              let snapshot := seq_state_snapshot (instruction_boundary tnil regs) sigma in
              Some (regs, sigma, [SWriteMem address' value' snapshot],
                conditions ++
                  [bv_unsigned address' + Z.of_N len <= 2 ^ 64;
                   set_Forall (fun a =>
                     ~ (bv_unsigned address' <= bv_unsigned a <
                        bv_unsigned address' + Z.of_N len)) (dom sigma.(seq_mem))])
          end
      | _ => None
      end
  | _ => None
  end.

Lemma exec_memory_read address value kind len tag ann regs sigma
    regs' sigma' labels conditions trace :
  exec_memory_event (ReadMem (RVal_Bits value) kind (RVal_Bits address) len tag ann)
    regs sigma = Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions ->
  seq_step
    (instruction_boundary
      (ReadMem (RVal_Bits value) kind (RVal_Bits address) len tag ann :t: trace) regs)
    sigma labels (instruction_boundary trace regs') sigma' [].
Proof.
  unfold exec_memory_event.
  destruct (read_mem (seq_mem sigma)
    (bv_unsigned (Z_to_bv 64 (bvn_unsigned address))) len) as [memory|] eqn:Hread;
    [|discriminate].
  intros Heq Hconditions. inversion Heq; subst; clear Heq.
  unfold ExecutorConditions in Hconditions.
  repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst end.
  eapply SeqStep with
    (κ := Some (LReadMem (RVal_Bits value) kind (RVal_Bits address) len tag))
    (κ' := None).
  - reflexivity.
  - constructor.
  - exists (Z_to_bv 64 (bvn_unsigned address)),
      (Z_to_bv (8 * len) (bvn_unsigned value)),
      (Z_to_bv (8 * len) (bvn_unsigned value)).
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    simpl. rewrite Hread. repeat split; auto.
Qed.

Lemma exec_memory_write address value result kind len tag ann regs sigma
    regs' sigma' labels conditions trace :
  exec_memory_event
    (WriteMem result kind (RVal_Bits address) (RVal_Bits value) len tag ann)
    regs sigma = Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions ->
  seq_step
    (instruction_boundary
      (WriteMem result kind (RVal_Bits address) (RVal_Bits value) len tag ann :t: trace) regs)
    sigma labels (instruction_boundary trace regs') sigma' [].
Proof.
  unfold exec_memory_event.
  destruct (read_mem (seq_mem sigma)
    (bv_unsigned (Z_to_bv 64 (bvn_unsigned address))) len) as [memory|] eqn:Hread;
    intros Heq Hconditions; inversion Heq; subst; clear Heq;
    unfold ExecutorConditions in Hconditions;
    repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst end.
  - eapply SeqStep with
      (κ := Some (LWriteMem result kind (RVal_Bits address) (RVal_Bits value) len tag))
      (κ' := None).
    + reflexivity.
    + constructor.
    + exists (write_mem len (seq_mem sigma) (Z_to_bv 64 (bvn_unsigned address))
        (bv_unsigned (Z_to_bv (8 * len) (bvn_unsigned value)))),
        (Z_to_bv 64 (bvn_unsigned address)),
        (Z_to_bv (8 * len) (bvn_unsigned value)).
      split; [assumption|]. split; [assumption|]. split; [assumption|].
      simpl. rewrite Hread. repeat split; reflexivity.
  - eapply SeqStep with
      (κ := Some (LWriteMem result kind (RVal_Bits address) (RVal_Bits value) len tag))
      (κ' := Some (SWriteMem (Z_to_bv 64 (bvn_unsigned address))
        (Z_to_bv (8 * len) (bvn_unsigned value))
        (seq_state_snapshot (instruction_boundary tnil regs') sigma'))).
    + reflexivity.
    + constructor.
    + exists (seq_mem sigma'), (Z_to_bv 64 (bvn_unsigned address)),
        (Z_to_bv (8 * len) (bvn_unsigned value)).
      split; [assumption|]. split; [assumption|]. split; [assumption|].
      simpl. rewrite Hread. repeat split; auto.
Qed.

Definition exec_silent_event (e : event) (rest : isla_trace)
    (regs : reg_map) (sigma : seq_global_state) :
    option (isla_trace * ExecutorResult) :=
  match e with
  | Smt (DefineConst x expression) _ =>
      value ← eval_exp expression;
      Some (subst_trace value x rest, (regs, sigma, [], []))
  | Smt (Assert expression) _ =>
      match eval_exp expression with
      | Some (Val_Bool true) =>
          Some (rest, (regs, sigma, [], [eval_exp expression = Some (Val_Bool true)]))
      | _ => None
      end
  | Assume expression _ =>
      match eval_a_exp regs expression with
      | Some (Val_Bool true) =>
          Some (rest,
            (regs, sigma, [], [eval_a_exp regs expression = Some (Val_Bool true)]))
      | _ => None
      end
  | BranchAddress _ _ | Branch _ _ _ | Barrier _ _ | AbstractPrimop _ _ _ _ =>
      Some (rest, (regs, sigma, [], []))
  | _ => None
  end.

Lemma exec_define_constant x expression ann rest regs sigma trace'
    regs' sigma' labels conditions :
  exec_silent_event (Smt (DefineConst x expression) ann) rest regs sigma =
    Some (trace', (regs', sigma', labels, conditions)) ->
  seq_step
    (instruction_boundary (Smt (DefineConst x expression) ann :t: rest) regs)
    sigma labels (instruction_boundary trace' regs') sigma' [].
Proof.
  unfold exec_silent_event.
  destruct (eval_exp expression) as [value|] eqn:Hvalue; simpl; [|discriminate].
  intros Heq. inversion Heq; subst; clear Heq.
  eapply SeqStep with (κ := None) (κ' := None).
  - reflexivity.
  - constructor. exact Hvalue.
  - repeat split; reflexivity.
Qed.

Lemma executor_assume expression ann rest regs sigma :
  eval_a_exp regs expression = Some (Val_Bool true) ->
  seq_step (instruction_boundary (Assume expression ann :t: rest) regs)
    sigma [] (instruction_boundary rest regs) sigma [].
Proof.
  intros Hvalue.
  eapply SeqStep with (κ := Some (LAssume true)) (κ' := None).
  - reflexivity.
  - constructor. exact Hvalue.
  - repeat split; reflexivity.
Qed.

Lemma executor_assert expression ann rest regs sigma :
  eval_exp expression = Some (Val_Bool true) ->
  seq_step (instruction_boundary (Smt (Assert expression) ann :t: rest) regs)
    sigma [] (instruction_boundary rest regs) sigma [].
Proof.
  intros Hvalue.
  eapply SeqStep with (κ := Some (LAssert true)) (κ' := None).
  - reflexivity.
  - constructor. exact Hvalue.
  - repeat split; reflexivity.
Qed.

Lemma exec_silent_event_sound e rest regs sigma trace' regs' sigma' labels conditions :
  exec_silent_event e rest regs sigma =
    Some (trace', (regs', sigma', labels, conditions)) ->
  seq_step (instruction_boundary (e :t: rest) regs) sigma labels
    (instruction_boundary trace' regs') sigma' [].
Proof.
  destruct e; simpl; try discriminate.
  all: try (intros Heq; inversion Heq; subst; clear Heq;
    eapply SeqStep with (κ' := None);
      [reflexivity|constructor|repeat split; reflexivity]).
  - destruct smt5; simpl; try discriminate.
    + apply exec_define_constant.
    + destruct (eval_exp exp5) as [value|] eqn:Hvalue; [|discriminate].
      destruct value; try discriminate. destruct bool5; try discriminate.
      intros Heq; inversion Heq; subst; clear Heq.
      apply executor_assert. exact Hvalue.
  - destruct (eval_a_exp regs a_exp5) as [value|] eqn:Hvalue; [|discriminate].
    destruct value; try discriminate. destruct bool5; try discriminate.
    intros Heq; inversion Heq; subst; clear Heq.
    apply executor_assume. exact Hvalue.
Qed.

Lemma exec_memory_event_sound e regs sigma regs' sigma' labels conditions trace :
  exec_memory_event e regs sigma = Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions ->
  seq_step (instruction_boundary (e :t: trace) regs) sigma labels
    (instruction_boundary trace regs') sigma' [].
Proof.
  destruct e; simpl; try discriminate.
  all: destruct addr; try discriminate; destruct base_val5; try discriminate.
  - destruct valu5; try discriminate; destruct base_val5; try discriminate.
    apply exec_memory_read.
  - destruct data; try discriminate; destruct base_val5; try discriminate.
    apply exec_memory_write.
Qed.

Definition exec_declaration (x : var_name) (ty : ty) (rest : isla_trace)
    (regs : reg_map) (sigma : seq_global_state) : option isla_trace :=
  let witness := declaration_read (isla_trace_length rest) x rest regs sigma in
  match ty with
  | Ty_BitVec n =>
      let value := match witness with
        | Some (Val_Bits value) => Z_to_bv n (bvn_unsigned value)
        | _ => Z_to_bv n 0
        end in
      Some (subst_trace (Val_Bits value) x rest)
  | Ty_Bool =>
      let value := match witness with Some (Val_Bool value) => value | _ => false end in
      Some (subst_trace (Val_Bool value) x rest)
  | Ty_Enum _ =>
      let value := match witness with Some (Val_Enum value) => value | _ => "" end in
      Some (subst_trace (Val_Enum value) x rest)
  | _ => None
  end.

(** Reject infeasible data conditions before selecting a branch. *)
Definition executor_bits_eqb (x y : bvn) : bool :=
  N.eqb x.(bvn_n) y.(bvn_n) && Z.eqb (bvn_unsigned x) (bvn_unsigned y).

Definition executor_base_eqb (x y : base_val) : bool :=
  match x, y with
  | Val_Symbolic a, Val_Symbolic b => Z.eqb a b
  | Val_Bool a, Val_Bool b => Bool.eqb a b
  | Val_Bits a, Val_Bits b => executor_bits_eqb a b
  | Val_Enum a, Val_Enum b => String.eqb a b
  | _, _ => false
  end.

Fixpoint executor_valu_eqb (x y : valu) : bool :=
  match x, y with
  | RegVal_Base a, RegVal_Base b => executor_base_eqb a b
  | RegVal_I a b, RegVal_I c d => Z.eqb a c && Z.eqb b d
  | RegVal_String a, RegVal_String b => String.eqb a b
  | RegVal_Unit, RegVal_Unit | RegVal_Poison, RegVal_Poison => true
  | RegVal_Vector xs, RegVal_Vector ys | RegVal_List xs, RegVal_List ys =>
      (fix equal (xs ys : list valu) :=
        match xs, ys with
        | [], [] => true
        | a :: xs, b :: ys => executor_valu_eqb a b && equal xs ys
        | _, _ => false
        end) xs ys
  | RegVal_Struct xs, RegVal_Struct ys =>
      (fix equal (xs ys : list (sail_name * valu)) :=
        match xs, ys with
        | [], [] => true
        | a :: xs, b :: ys => String.eqb a.1 b.1 &&
            executor_valu_eqb a.2 b.2 && equal xs ys
        | _, _ => false
        end) xs ys
  | RegVal_Constructor a x, RegVal_Constructor b y =>
      String.eqb a b && executor_valu_eqb x y
  | _, _ => false
  end.

Definition executor_option_valu_eqb (x y : option valu) : bool :=
  match x, y with
  | Some a, Some b => executor_valu_eqb a b
  | None, None => true
  | _, _ => false
  end.

Lemma executor_bits_eqb_reflect x y : executor_bits_eqb x y = true <-> x = y.
Proof. unfold executor_bits_eqb. rewrite andb_true_iff N.eqb_eq Z.eqb_eq. symmetry. apply bvn_eq. Qed.
Lemma executor_base_eqb_reflect x y : executor_base_eqb x y = true <-> x = y.
Proof.
  destruct x, y; simpl; try (split; [discriminate|congruence]);
    rewrite ?Z.eqb_eq ?Bool.eqb_true_iff ?executor_bits_eqb_reflect ?String.eqb_eq;
    split; intros; congruence.
Qed.
Lemma executor_valu_eqb_reflect x y : executor_valu_eqb x y = true <-> x = y.
Proof.
  revert x y. fix IH 1. intros x y. destruct x, y; simpl;
    try (split; [discriminate|congruence]);
    rewrite ?executor_base_eqb_reflect ?andb_true_iff ?Z.eqb_eq ?String.eqb_eq;
    try (split; intros; congruence).
  - clear IH. naive_solver.
  - revert l0. induction l as [|a l IHlist]; intros [|b l0]; simpl; try done;
      try (split; [discriminate|congruence]).
    rewrite andb_true_iff (IH a b) IHlist. clear IH. naive_solver.
  - revert l0. induction l as [|a l IHlist]; intros [|b l0]; simpl; try done;
      try (split; [discriminate|congruence]).
    rewrite andb_true_iff (IH a b) IHlist. clear IH. naive_solver.
  - revert l0. induction l as [|[name a] l IHlist]; intros [|[name' b] l0]; simpl; try done;
      try (split; [discriminate|congruence]).
    rewrite !andb_true_iff String.eqb_eq (IH a b) IHlist. clear IH. naive_solver.
  - rewrite (IH x y). clear IH. naive_solver.
Qed.


Definition executor_write_disjointb (address : bv 64) (len : N)
    (sigma : seq_global_state) : bool :=
  forallb (fun entry => negb
    (Z.leb (bv_unsigned address) (bv_unsigned entry.1) &&
     Z.ltb (bv_unsigned entry.1) (bv_unsigned address + Z.of_N len)))
    (map_to_list sigma.(seq_mem)).

Lemma executor_write_disjointb_reflect address len sigma :
  executor_write_disjointb address len sigma = true <->
  set_Forall (fun a => ~ (bv_unsigned address <= bv_unsigned a <
    bv_unsigned address + Z.of_N len)) (dom sigma.(seq_mem)).
Proof.
  unfold executor_write_disjointb.
  rewrite <-Is_true_true. rewrite forallb_True Forall_forall. unfold set_Forall.
  split.
  - intros H a Hdom. apply elem_of_dom in Hdom. destruct Hdom as [value Hvalue].
    specialize (H (a, value)). simpl in H.
    assert ((a, value) ∈ map_to_list (seq_mem sigma)) as Hin by
      (apply elem_of_map_to_list; exact Hvalue).
    specialize (H Hin).
    apply Is_true_true in H.
    rewrite negb_true_iff andb_false_iff Z.leb_gt Z.ltb_ge in H. lia.
  - intros H [a value] Hin. apply elem_of_map_to_list in Hin. simpl.
    apply Is_true_true.
    rewrite negb_true_iff andb_false_iff Z.leb_gt Z.ltb_ge.
    assert (a ∈ dom (seq_mem sigma)) as Hdom by
      (apply elem_of_dom; exists value; exact Hin).
    specialize (H a Hdom). lia.
Qed.
Lemma executor_option_valu_eqb_reflect x y :
  executor_option_valu_eqb x y = true <-> x = y.
Proof.
  destruct x as [a|], y as [b|]; simpl;
    try (split; [discriminate|congruence]); try done.
  rewrite executor_valu_eqb_reflect. split; intros; congruence.
Qed.

Definition exec_event_feasibleb (e : event) (regs : reg_map)
    (sigma : seq_global_state) : bool :=
  match e with
  | ReadReg name al pattern _ =>
      match regs !! name with
      | Some actual => executor_option_valu_eqb (read_accessor al actual) (read_accessor al pattern)
      | None => false
      end
  | AssumeReg name al value _ =>
      match regs !! name with
      | Some actual => executor_option_valu_eqb (read_accessor al actual) (Some value)
      | None => false
      end
  | ReadMem data _ (RVal_Bits address) len _ _ =>
      match data with
      | RVal_Bits value =>
          let address' := Z_to_bv 64 (bvn_unsigned address) in
          let value' := Z_to_bv (8 * len) (bvn_unsigned value) in
          executor_bits_eqb address (bv_to_bvn address') &&
          executor_bits_eqb value (bv_to_bvn value') &&
          bool_decide (0 < Z.of_N len) &&
          match read_mem sigma.(seq_mem) (bv_unsigned address') len with
          | Some memory => executor_bits_eqb memory (bv_to_bvn value')
          | None => false
          end
      | _ => false
      end
  | WriteMem _ _ (RVal_Bits address) data len _ _ =>
      match data with
      | RVal_Bits value =>
          let address' := Z_to_bv 64 (bvn_unsigned address) in
          let value' := Z_to_bv (8 * len) (bvn_unsigned value) in
          executor_bits_eqb address (bv_to_bvn address') &&
          executor_bits_eqb value (bv_to_bvn value') &&
          bool_decide (0 < Z.of_N len) &&
          match read_mem sigma.(seq_mem) (bv_unsigned address') len with
          | Some _ => true
          | None =>
              bool_decide (bv_unsigned address' + Z.of_N len <= 2 ^ 64) &&
              executor_write_disjointb address' len sigma
          end
      | _ => false
      end
  | _ => true
  end.

Definition exec_nondeclaration_event (e : event) (rest : isla_trace) (regs : reg_map)
    (sigma : seq_global_state) : option (isla_trace * ExecutorResult) :=
  if exec_event_feasibleb e regs sigma then
  match exec_silent_event e rest regs sigma with
  | Some result => Some result
  | None =>
      match exec_register_event e regs sigma with
      | Some result => Some (rest, result)
      | None => (fun result => (rest, result)) <$> exec_memory_event e regs sigma
      end
  end else None.

Definition exec_event (e : event) (rest : isla_trace) (regs : reg_map)
    (sigma : seq_global_state) : option (isla_trace * ExecutorResult) :=
  match e with
  | Smt (DeclareConst x ty) _ =>
      trace ← exec_declaration x ty rest regs sigma;
      Some (trace, (regs, sigma, [], []))
  | _ => exec_nondeclaration_event e rest regs sigma
  end.

Lemma exec_declaration_sound x ty ann rest regs sigma trace' :
  exec_declaration x ty rest regs sigma = Some trace' ->
  seq_step (instruction_boundary (Smt (DeclareConst x ty) ann :t: rest) regs)
    sigma [] (instruction_boundary trace' regs) sigma [].
Proof.
  unfold exec_declaration. destruct ty; try discriminate; intros [= <-].
  - apply executor_declare_bool.
  - apply executor_declare_bits.
  - apply executor_declare_enum.
Qed.

Lemma exec_nondeclaration_event_sound e rest regs sigma trace'
    regs' sigma' labels conditions :
  exec_nondeclaration_event e rest regs sigma =
    Some (trace', (regs', sigma', labels, conditions)) ->
  ExecutorConditions conditions ->
  seq_step (instruction_boundary (e :t: rest) regs) sigma labels
    (instruction_boundary trace' regs') sigma' [].
Proof.
  unfold exec_nondeclaration_event.
  destruct (exec_event_feasibleb e regs sigma); [|discriminate].
  destruct (exec_silent_event e rest regs sigma) as [result|] eqn:Hsilent.
  - intros Heq _. inversion Heq; subst; clear Heq.
    eapply exec_silent_event_sound. exact Hsilent.
  - destruct (exec_register_event e regs sigma) as [result|] eqn:Hregister.
    + intros Heq Hconditions. inversion Heq; subst; clear Heq.
      eapply exec_register_event_sound; eauto.
    + destruct (exec_memory_event e regs sigma) as [result|] eqn:Hmemory;
        simpl; [|discriminate].
      intros Heq Hconditions. inversion Heq; subst; clear Heq.
      eapply exec_memory_event_sound; eauto.
Qed.

Lemma exec_event_sound e rest regs sigma trace' regs' sigma' labels conditions :
  exec_event e rest regs sigma =
    Some (trace', (regs', sigma', labels, conditions)) ->
  ExecutorConditions conditions ->
  seq_step (instruction_boundary (e :t: rest) regs) sigma labels
    (instruction_boundary trace' regs') sigma' [].
Proof.
  destruct e; try apply exec_nondeclaration_event_sound.
  destruct smt5; try apply exec_nondeclaration_event_sound.
  cbn [exec_event].
  destruct (exec_declaration vvar5 ty5 rest regs sigma) as [next|] eqn:Hdeclaration;
    simpl; [|discriminate].
  intros Heq _. inversion Heq; subst; clear Heq.
  eapply exec_declaration_sound. exact Hdeclaration.
Qed.

Fixpoint first_result {A B} (f : A -> option B) (xs : list A) : option B :=
  match xs with
  | [] => None
  | x :: rest => match f x with Some result => Some result | None => first_result f rest end
  end.

Lemma first_result_member {A B} (f : A -> option B) xs result :
  first_result f xs = Some result -> exists x, x ∈ xs /\ f x = Some result.
Proof.
  induction xs as [|x xs IH]; simpl; [discriminate|].
  destruct (f x) as [value|] eqn:Hvalue.
  - intros [= <-]. exists x. split; [apply elem_of_cons; auto|exact Hvalue].
  - intros Hresult. destruct (IH Hresult) as [y [Hy Hvalue']].
    exists y. split; [apply elem_of_cons; auto|exact Hvalue'].
Qed.

Fixpoint exec_trace (fuel : nat) (trace : isla_trace) (regs : reg_map)
    (sigma : seq_global_state) : option ExecutorResult :=
  match fuel with
  | O => None
  | S fuel' =>
      match trace with
      | tnil => Some (regs, sigma, [], [])
      | e :t: rest =>
          step ← exec_event e rest regs sigma;
          let '(next, (regs', sigma', labels, conditions)) := step in
          result ← exec_trace fuel' next regs' sigma';
          let '(regs'', sigma'', tail, conditions') := result in
          Some (regs'', sigma'', labels ++ tail, conditions ++ conditions')
      | tcases branches => first_result (fun branch => exec_trace fuel' branch regs sigma) branches
      end
  end.

Lemma executor_cases branch branches regs sigma :
  branch ∈ branches ->
  seq_step (instruction_boundary (tcases branches) regs) sigma []
    (instruction_boundary branch regs) sigma [].
Proof.
  intros Hbranch. eapply SeqStep with (κ := None) (κ' := None).
  - reflexivity.
  - constructor. exact Hbranch.
  - repeat split; reflexivity.
Qed.

Lemma exec_trace_sound fuel trace regs sigma regs' sigma' labels conditions :
  exec_trace fuel trace regs sigma = Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions ->
  exists n, InstructionPrefix n (instruction_boundary trace regs) sigma labels
    (instruction_boundary tnil regs') sigma'.
Proof.
  revert trace regs sigma regs' sigma' labels conditions.
  induction fuel as [|fuel IH]; intros trace regs sigma regs' sigma' labels conditions;
    [discriminate|].
  destruct trace as [|e rest|branches].
  - cbn [exec_trace]. intros [= <- <- <- <-] _. exists 0%nat. constructor.
  - cbn [exec_trace].
    destruct (exec_event e rest regs sigma)
      as [[next [[[middle_regs middle_sigma] head] head_conditions]]|] eqn:Hstep;
      simpl; [|discriminate].
    destruct (exec_trace fuel next middle_regs middle_sigma)
      as [[[[final_regs final_sigma] tail] tail_conditions]|] eqn:Htail;
      simpl; [|discriminate].
    intros Heq Hconditions. inversion Heq; subst; clear Heq.
    apply Forall_app in Hconditions. destruct Hconditions as [Hhead Htail_conditions].
    destruct (IH _ _ _ _ _ _ _ Htail Htail_conditions) as [n Hprefix].
    exists (S n). econstructor.
    + discriminate.
    + eapply exec_event_sound; eauto.
    + reflexivity.
    + exact Hprefix.
  - cbn [exec_trace]. intros Hresult Hconditions.
    destruct (first_result_member _ _ _ Hresult) as [branch [Hbranch Hexec]].
    destruct (IH _ _ _ _ _ _ _ Hexec Hconditions) as [n Hprefix].
    exists (S n).
    change (InstructionPrefix (S n) (instruction_boundary (tcases branches) regs)
      sigma ([] ++ labels) (instruction_boundary tnil regs') sigma').
    econstructor.
    + discriminate.
    + apply executor_cases. exact Hbranch.
    + reflexivity.
    + exact Hprefix.
Qed.

Definition exec_finish (regs : reg_map) (sigma : seq_global_state) :
    option (seq_local_state * list seq_label * list Prop) :=
  match regs !! "PC" with
  | Some (RVal_Bits address) =>
      let pc := Z_to_bv 64 (bvn_unsigned address) in
      let conditions := [regs !! "PC" = Some (RVal_Bits pc)] in
      match sigma.(seq_instrs) !! pc with
      | Some next => Some (instruction_boundary next regs, [], conditions)
      | None =>
          Some (instruction_boundary tnil regs <| seq_nb_state := true |>,
            [SInstrTrap pc (seq_state_snapshot (instruction_boundary tnil regs) sigma)],
            conditions)
      end
  | _ => None
  end.

Definition exec_instr (trace : isla_trace) (regs : reg_map)
    (sigma : seq_global_state) : option ExecutorResult :=
  result ← exec_trace (S (isla_trace_length trace)) trace regs sigma;
  let '(regs', sigma', labels, conditions) := result in
  result' ← exec_finish regs' sigma';
  let '(_, last, conditions') := result' in
  Some (regs', sigma', labels ++ last, conditions ++ conditions').

Lemma exec_finish_sound regs sigma theta labels conditions :
  exec_finish regs sigma = Some (theta, labels, conditions) ->
  ExecutorConditions conditions ->
  seq_regs theta = regs /\
  seq_step (instruction_boundary tnil regs) sigma labels theta sigma [].
Proof.
  unfold exec_finish.
  destruct (regs !! "PC") as [value|] eqn:Hpc; [|discriminate].
  destruct value; try discriminate. destruct base_val5; try discriminate.
  destruct (seq_instrs sigma !! Z_to_bv 64 (bvn_unsigned bv5)) as [next|] eqn:Hnext;
    intros Heq Hconditions; inversion Heq; subst; clear Heq;
    inversion Hconditions; subst; split; [reflexivity| |reflexivity|].
  - eapply SeqStep with (κ := Some (LDone next)) (κ' := None).
    + reflexivity.
    + constructor.
    + split; [reflexivity|]. exists (Z_to_bv 64 (bvn_unsigned bv5)).
      split; [simpl; rewrite Hpc; assumption|].
      simpl. rewrite Hnext. repeat split; reflexivity.
  - eapply SeqStep with (κ := Some (LDone tnil))
      (κ' := Some (SInstrTrap (Z_to_bv 64 (bvn_unsigned bv5))
        (seq_state_snapshot (instruction_boundary tnil regs) sigma))).
    + reflexivity.
    + constructor.
    + split; [reflexivity|]. exists (Z_to_bv 64 (bvn_unsigned bv5)).
      split; [simpl; rewrite Hpc; assumption|].
      simpl. rewrite Hnext. repeat split; reflexivity.
Qed.

Theorem exec_instr_sound trace regs sigma regs' sigma' labels conditions :
  exec_instr trace regs sigma = Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions ->
  exists theta,
    seq_regs theta = regs' /\
    CompletedInstructionSegment (instruction_boundary trace regs) sigma labels theta sigma'.
Proof.
  unfold exec_instr.
  destruct (exec_trace (S (isla_trace_length trace)) trace regs sigma)
    as [[[[final_regs final_sigma] prefix] prefix_conditions]|] eqn:Htrace;
    simpl; [|discriminate].
  destruct (exec_finish final_regs final_sigma)
    as [[[theta last] last_conditions]|] eqn:Hfinish;
    simpl; [|discriminate].
  intros Heq Hconditions. inversion Heq; subst; clear Heq.
  apply Forall_app in Hconditions. destruct Hconditions as [Hprefix_conditions Hlast_conditions].
  destruct (exec_trace_sound _ _ _ _ _ _ _ _ Htrace Hprefix_conditions) as [n Hprefix].
  destruct (exec_finish_sound _ _ _ _ _ Hfinish Hlast_conditions) as [Hregs Hstep].
  exists theta. split; [exact Hregs|].
  exists n, (instruction_boundary tnil regs'), sigma', prefix, last.
  repeat split; auto.
Qed.

Print Assumptions instruction_prefix_append.
Print Assumptions instruction_prefix_completed.
Print Assumptions executor_declare_bits.
Print Assumptions executor_declare_bool.
Print Assumptions completed_instruction_nsteps.
Print Assumptions exec_register_read.
Print Assumptions exec_register_assume.
Print Assumptions exec_register_write.
Print Assumptions exec_register_event_sound.
Print Assumptions exec_memory_read.
Print Assumptions exec_memory_write.
Print Assumptions exec_define_constant.
Print Assumptions executor_assume.
Print Assumptions executor_assert.
Print Assumptions exec_silent_event_sound.
Print Assumptions exec_memory_event_sound.
Print Assumptions exec_declaration_sound.
Print Assumptions exec_event_sound.
Print Assumptions exec_trace_sound.
Print Assumptions exec_instr_sound.

Print Assumptions executor_bits_eqb_reflect.
Print Assumptions executor_base_eqb_reflect.
Print Assumptions executor_valu_eqb_reflect.
Print Assumptions executor_option_valu_eqb_reflect.
Print Assumptions executor_write_disjointb_reflect.

Print Assumptions executor_nsteps_append.
Print Assumptions completed_run_append.
Print Assumptions completed_run_nsteps.
