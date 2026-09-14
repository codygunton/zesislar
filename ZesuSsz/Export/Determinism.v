Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Export.Executor.
Require Import isla.opsem.

Definition event_declares (e : event) : bool :=
  match e with Smt (DeclareConst _ _) _ => true | _ => false end.

Lemma trace_event_deterministic e rest regs label next label' next' :
  event_declares e = false ->
  trace_step (e :t: rest) regs label next ->
  trace_step (e :t: rest) regs label' next' ->
  label = label' /\ next = next'.
Proof.
  destruct e; try destruct smt5; simpl; try discriminate;
    intros _ Hstep Hstep'; inversion Hstep; inversion Hstep'; subst;
    split; congruence.
Qed.

Lemma event_declares_reflect e :
  event_declares e = false <->
  forall x ty ann, e <> Smt (DeclareConst x ty) ann.
Proof.
  destruct e; try destruct smt5; simpl;
    split; intros H; try congruence; try discriminate.
  exfalso. apply (H vvar5 ty5 annot5). reflexivity.
Qed.

Definition memory_read_backed (e : event) (sigma : seq_global_state) : Prop :=
  match e with
  | ReadMem _ _ address len _ _ =>
      match address with
      | RVal_Bits bits =>
          exists pointer value,
            bvn_to_bv 64 bits = Some pointer /\
            read_mem sigma.(seq_mem) (bv_unsigned pointer) len = Some value
      | _ => False
      end
  | _ => True
  end.

Definition memory_read_backedb (e : event) (sigma : seq_global_state) : bool :=
  match e with
  | ReadMem _ _ address len _ _ =>
      match address with
      | RVal_Bits bits =>
          match bvn_to_bv 64 bits with
          | Some pointer =>
              match read_mem sigma.(seq_mem) (bv_unsigned pointer) len with
              | Some _ => true
              | None => false
              end
          | None => false
          end
      | _ => false
      end
  | _ => true
  end.

Lemma memory_read_backed_reflect e sigma :
  memory_read_backedb e sigma = true <-> memory_read_backed e sigma.
Proof.
  destruct e; simpl; try tauto.
  destruct addr; simpl; try (split; [discriminate|contradiction]).
  destruct base_val5; simpl; try (split; [discriminate|contradiction]).
  destruct (bvn_to_bv 64 bv5) as [pointer|] eqn:Hpointer.
  - destruct (read_mem (seq_mem sigma) (bv_unsigned pointer) num_bytes)
      as [value|] eqn:Hread.
    + split; intros _; [exists pointer, value; auto|reflexivity].
    + split; [discriminate|]. intros [p [value [Heq Hvalue]]].
      inversion Heq; subst. congruence.
  - split; [discriminate|]. intros [p [value [Heq _]]]. discriminate.
Qed.

Global Instance memory_read_backed_decision e sigma : Decision (memory_read_backed e sigma).
Proof.
  destruct (memory_read_backedb e sigma) eqn:Hbacked.
  - left. apply memory_read_backed_reflect. exact Hbacked.
  - right. intros H. apply memory_read_backed_reflect in H. congruence.
Defined.

Print Assumptions trace_event_deterministic.
Print Assumptions event_declares_reflect.
Print Assumptions memory_read_backed_reflect.

(** Syntactically unused declarations do not depend on their witness. *)
Definition base_unusedb (x : var_name) (value : base_val) : bool :=
  match value with
  | Val_Symbolic y => negb (Z.eqb y x)
  | _ => true
  end.
Definition base_unused (x : var_name) (value : base_val) : Prop :=
  match value with
  | Val_Symbolic y => y <> x
  | _ => True
  end.
Lemma base_unused_reflect x value :
  base_unusedb x value = true <-> base_unused x value.
Proof.
  destruct value; simpl; try tauto.
  rewrite negb_true_iff Z.eqb_neq. reflexivity.
Qed.
Lemma base_unused_substitution x value replacement :
  base_unusedb x value = true -> subst_val_base_val replacement x value = value.
Proof.
  destruct value; simpl; intros H; try reflexivity.
  unfold eq_var_name. rewrite negb_true_iff in H. rewrite H. reflexivity.
Qed.
Print Assumptions base_unused_reflect.
Print Assumptions base_unused_substitution.

Fixpoint valu_unusedb (x : var_name) (value : valu) {struct value} : bool :=
  match value with
  | RegVal_Base base => base_unusedb x base
  | RegVal_Vector values | RegVal_List values => forallb (valu_unusedb x) values
  | RegVal_Struct fields => forallb (fun field => valu_unusedb x field.2) fields
  | RegVal_Constructor _ value => valu_unusedb x value
  | _ => true
  end.
Fixpoint valu_unused (x : var_name) (value : valu) {struct value} : Prop :=
  match value with
  | RegVal_Base base => base_unused x base
  | RegVal_Vector values | RegVal_List values => (fix all (values : list valu) :=
        match values with
        | [] => True
        | value :: values => valu_unused x value /\ all values
        end) values
  | RegVal_Struct fields => (fix all (fields : list (sail_name * valu)) :=
        match fields with
        | [] => True
        | (_, value) :: fields => valu_unused x value /\ all fields
        end) fields
  | RegVal_Constructor _ value => valu_unused x value
  | _ => True
  end.
Lemma valu_unused_reflect x value :
  valu_unusedb x value = true <-> valu_unused x value.
Proof.
  revert value. fix IH 1. intros value. destruct value; simpl; try tauto.
  - apply base_unused_reflect.
  - induction l as [|a l IHlist]; simpl; [split; intros; constructor|].
    rewrite andb_true_iff (IH a) IHlist. reflexivity.
  - induction l as [|a l IHlist]; simpl; [split; intros; constructor|].
    rewrite andb_true_iff (IH a) IHlist. reflexivity.
  - induction l as [|[name a] l IHlist]; simpl; [split; intros; constructor|].
    rewrite andb_true_iff (IH a) IHlist. reflexivity.
  - apply IH.
Qed.
Print Assumptions valu_unused_reflect.

Lemma valu_unused_substitution x value replacement :
  valu_unusedb x value = true -> subst_val_valu replacement x value = value.
Proof.
  revert value. fix IH 1. intros value. destruct value; simpl; intros H; try reflexivity.
  - rewrite (base_unused_substitution x base_val5 replacement H). reflexivity.
  - f_equal. induction l as [|a l IHlist]; simpl in *; [reflexivity|].
    apply andb_true_iff in H as [Ha Hl]. rewrite (IH a Ha) (IHlist Hl). reflexivity.
  - f_equal. induction l as [|a l IHlist]; simpl in *; [reflexivity|].
    apply andb_true_iff in H as [Ha Hl]. rewrite (IH a Ha) (IHlist Hl). reflexivity.
  - f_equal. induction l as [|[name a] l IHlist]; simpl in *; [reflexivity|].
    apply andb_true_iff in H as [Ha Hl]. rewrite (IH a Ha) (IHlist Hl). reflexivity.
  - rewrite (IH value H). reflexivity.
Qed.
Print Assumptions valu_unused_substitution.

Fixpoint exp_unusedb (x : var_name) (expression : exp) {struct expression} : bool :=
  match expression with
  | Val value _ => base_unusedb x value
  | Unop _ expression _ => exp_unusedb x expression
  | Binop _ lhs rhs _ => exp_unusedb x lhs && exp_unusedb x rhs
  | Manyop _ expressions _ => forallb (exp_unusedb x) expressions
  | Ite condition yes no _ => exp_unusedb x condition && exp_unusedb x yes && exp_unusedb x no
  end.
Fixpoint exp_unused (x : var_name) (expression : exp) {struct expression} : Prop :=
  match expression with
  | Val value _ => base_unused x value
  | Unop _ expression _ => exp_unused x expression
  | Binop _ lhs rhs _ => exp_unused x lhs /\ exp_unused x rhs
  | Manyop _ expressions _ =>
      (fix all (expressions : list exp) :=
        match expressions with
        | [] => True
        | expression :: expressions => exp_unused x expression /\ all expressions
        end) expressions
  | Ite condition yes no _ => exp_unused x condition /\ exp_unused x yes /\ exp_unused x no
  end.
Lemma exp_unused_reflect x expression :
  exp_unusedb x expression = true <-> exp_unused x expression.
Proof.
  revert expression. fix IH 1. intros expression. destruct expression; simpl.
  - apply base_unused_reflect.
  - apply IH.
  - rewrite andb_true_iff (IH expression1) (IH expression2). reflexivity.
  - induction l as [|a l IHlist]; simpl; [tauto|].
    rewrite andb_true_iff (IH a) IHlist. reflexivity.
  - rewrite !andb_true_iff (IH expression1) (IH expression2) (IH expression3). tauto.
Qed.
Lemma exp_unused_substitution x expression replacement :
  exp_unusedb x expression = true -> subst_val_exp replacement x expression = expression.
Proof.
  revert expression. fix IH 1. intros expression. destruct expression; simpl; intros H.
  - rewrite (base_unused_substitution x base_val5 replacement H). reflexivity.
  - rewrite (IH expression H). reflexivity.
  - apply andb_true_iff in H as [Hl Hr].
    rewrite (IH expression1 Hl) (IH expression2 Hr). reflexivity.
  - f_equal. induction l as [|a l IHlist]; simpl in *; [reflexivity|].
    apply andb_true_iff in H as [Ha Hl]. rewrite (IH a Ha) (IHlist Hl). reflexivity.
  - apply andb_true_iff in H as [Hcy Hn]. apply andb_true_iff in Hcy as [Hc Hy].
    rewrite (IH expression1 Hc) (IH expression2 Hy) (IH expression3 Hn). reflexivity.
Qed.
Print Assumptions exp_unused_reflect.
Print Assumptions exp_unused_substitution.

Definition event_unusedb (x : var_name) (e : event) : bool :=
  match e with
  | Smt (DefineConst _ expression) _ | Smt (Assert expression) _ => exp_unusedb x expression
  | ReadReg _ _ value _ | WriteReg _ _ value _ | AssumeReg _ _ value _
  | BranchAddress value _ | Barrier value _ | Instr value _
  | FunAssume _ value _ _ | UseFunAssume _ value _ _
  | AbstractCall _ value _ _ | AbstractPrimop _ value _ _ => valu_unusedb x value
  | ReadMem value kind address _ _ _ =>
      valu_unusedb x value && valu_unusedb x kind && valu_unusedb x address
  | WriteMem result kind address data _ _ _ =>
      valu_unusedb x result && valu_unusedb x kind && valu_unusedb x address && valu_unusedb x data
  | CacheOp kind address _ => valu_unusedb x kind && valu_unusedb x address
  | _ => true
  end.
Definition event_unused (x : var_name) (e : event) : Prop :=
  match e with
  | Smt (DefineConst _ expression) _ | Smt (Assert expression) _ => exp_unused x expression
  | ReadReg _ _ value _ | WriteReg _ _ value _ | AssumeReg _ _ value _
  | BranchAddress value _ | Barrier value _ | Instr value _
  | FunAssume _ value _ _ | UseFunAssume _ value _ _
  | AbstractCall _ value _ _ | AbstractPrimop _ value _ _ => valu_unused x value
  | ReadMem value kind address _ _ _ =>
      valu_unused x value /\ valu_unused x kind /\ valu_unused x address
  | WriteMem result kind address data _ _ _ =>
      valu_unused x result /\ valu_unused x kind /\ valu_unused x address /\ valu_unused x data
  | CacheOp kind address _ => valu_unused x kind /\ valu_unused x address
  | _ => True
  end.
Lemma event_unused_reflect x e : event_unusedb x e = true <-> event_unused x e.
Proof.
  destruct e; try destruct smt5; simpl;
    rewrite ?andb_true_iff ?valu_unused_reflect ?exp_unused_reflect; tauto.
Qed.
Lemma event_unused_substitution x e replacement :
  event_unusedb x e = true -> subst_val_event replacement x e = e.
Proof.
  destruct e; try destruct smt5; simpl; intros H;
    repeat match goal with H : _ && _ = true |- _ =>
      apply andb_true_iff in H as [? ?] end;
    repeat match goal with
    | H : valu_unusedb x ?value = true |- _ =>
        rewrite (valu_unused_substitution x value replacement H); clear H
    | H : exp_unusedb x ?expression = true |- _ =>
        rewrite (exp_unused_substitution x expression replacement H); clear H
    end; reflexivity.
Qed.
Print Assumptions event_unused_reflect.
Print Assumptions event_unused_substitution.

Fixpoint trace_unusedb (x : var_name) (trace : isla_trace) {struct trace} : bool :=
  match trace with
  | tnil => true
  | e :t: rest => event_unusedb x e && trace_unusedb x rest
  | tcases branches => forallb (trace_unusedb x) branches
  end.
Fixpoint trace_unused (x : var_name) (trace : isla_trace) {struct trace} : Prop :=
  match trace with
  | tnil => True
  | e :t: rest => event_unused x e /\ trace_unused x rest
  | tcases branches =>
      (fix all (branches : list isla_trace) :=
        match branches with
        | [] => True
        | branch :: branches => trace_unused x branch /\ all branches
        end) branches
  end.
Lemma trace_unused_reflect x trace : trace_unusedb x trace = true <-> trace_unused x trace.
Proof.
  revert trace. fix IH 1. intros [|e rest|branches]; simpl; [tauto| |].
  - rewrite andb_true_iff event_unused_reflect (IH rest). reflexivity.
  - induction branches as [|branch branches IHlist]; simpl; [tauto|].
    rewrite andb_true_iff (IH branch) IHlist. reflexivity.
Qed.
Lemma trace_unused_substitution x trace replacement :
  trace_unusedb x trace = true -> subst_trace replacement x trace = trace.
Proof.
  revert trace. fix IH 1. intros [|e rest|branches]; simpl; intros H; [reflexivity| |].
  - apply andb_true_iff in H as [He Hr].
    rewrite (event_unused_substitution x e replacement He) (IH rest Hr). reflexivity.
  - f_equal. induction branches as [|branch branches IHlist]; simpl in *; [reflexivity|].
    apply andb_true_iff in H as [Hb Hl]. rewrite (IH branch Hb). f_equal. exact (IHlist Hl).
Qed.
Print Assumptions trace_unused_reflect.
Print Assumptions trace_unused_substitution.

(** Reads preserve substitution and uniquely determine their witness. *)
Lemma list_find_idx_substitution x replacement name fields :
  list_find_idx (fun field : sail_name * valu => field.1 = name)
    (map (fun '(key, value) => (key, subst_val_valu replacement x value)) fields) =
  list_find_idx (fun field : sail_name * valu => field.1 = name) fields.
Proof.
  induction fields as [|[key value] fields IH]; simpl; [reflexivity|].
  destruct (decide (key = name)); simpl; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma read_accessor_substitution x replacement al value :
  read_accessor al (subst_val_valu replacement x value) =
  (subst_val_valu replacement x <$> read_accessor al value).
Proof.
  revert value. induction al as [|[name] al IH]; intros value; simpl; [reflexivity|].
  destruct value; simpl; try reflexivity.
  unfold read_accessor at 1 2. cbn -[read_accessor].
  rewrite list_find_idx_substitution.
  destruct (list_find_idx (fun field : sail_name * valu => field.1 = name) l)
    as [index|] eqn:Hindex; simpl; [|reflexivity].
  rewrite list_lookup_fmap.
  destruct (l !! index) as [[key field]|]; simpl; [apply IH|reflexivity].
Qed.
Print Assumptions read_accessor_substitution.

Lemma read_symbol_substitution x pattern replacement found :
  read_symbol x pattern (subst_val_valu replacement x pattern) = Some found ->
  found = replacement.
Proof.
  revert pattern found. fix IH 1. intros pattern found. destruct pattern; simpl; try discriminate.
  - destruct base_val5; simpl; try discriminate.
    destruct (bool_decide (x = vvar5)) eqn:Hxy; [|discriminate].
    apply bool_decide_eq_true in Hxy. subst vvar5. unfold eq_var_name.
    rewrite Z.eqb_refl. intros [= <-]. reflexivity.
  - induction l as [|[name value] rest IHlist]; simpl; [discriminate|].
    rewrite String.eqb_refl.
    destruct (read_symbol x value (subst_val_valu replacement x value))
      as [result|] eqn:Hread.
    + intros [= <-]. exact (IH value result Hread).
    + exact IHlist.
Qed.
Print Assumptions read_symbol_substitution.

Lemma read_symbol_pins x pattern actual replacement found :
  read_symbol x pattern actual = Some found ->
  subst_val_valu replacement x pattern = actual ->
  found = replacement.
Proof. intros Hread <-. exact (read_symbol_substitution x pattern replacement found Hread). Qed.
Print Assumptions read_symbol_pins.


(** Other substitutions preserve a concrete read witness. *)
Lemma read_symbol_substitution_actual x pattern actual replacement y :
  read_symbol x pattern (subst_val_valu replacement y actual) =
  (subst_val_base_val replacement y <$> read_symbol x pattern actual).
Proof.
  revert pattern actual. fix IH 1. intros pattern actual.
  destruct pattern; simpl; try reflexivity.
  - destruct base_val5; simpl; try reflexivity.
    destruct (bool_decide (x = vvar5)); [|reflexivity].
    destruct actual; simpl; reflexivity.
  - destruct actual; simpl; try reflexivity.
    revert l0. induction l as [|[name value] rest IHlist]; intros [|[actual_name actual_value] actual_rest];
      simpl; try reflexivity.
    destruct (String.eqb name actual_name); [|reflexivity].
    rewrite (IH value actual_value).
    destruct (read_symbol x value actual_value); simpl; [reflexivity|apply IHlist].
Qed.
Print Assumptions read_symbol_substitution_actual.

Definition base_ground (value : base_val) : Prop :=
  match value with Val_Symbolic _ => False | _ => True end.
Definition base_groundb (value : base_val) : bool :=
  match value with Val_Symbolic _ => false | _ => true end.
Lemma base_ground_reflect value : base_groundb value = true <-> base_ground value.
Proof. destruct value; simpl; split; intros; try discriminate; try contradiction; try reflexivity; exact I. Qed.
Lemma base_ground_substitution value replacement y :
  base_ground value -> subst_val_base_val replacement y value = value.
Proof. destruct value; simpl; intros H; [contradiction|reflexivity|reflexivity|reflexivity]. Qed.
Lemma read_symbol_ground_substitution x pattern actual replacement y found :
  read_symbol x pattern actual = Some found ->
  base_ground found ->
  read_symbol x pattern (subst_val_valu replacement y actual) = Some found.
Proof.
  intros Hread Hground. rewrite read_symbol_substitution_actual Hread. simpl.
  rewrite (base_ground_substitution found replacement y Hground). reflexivity.
Qed.
Fixpoint substitute_values (substitutions : list (base_val * var_name)) (value : valu) : valu :=
  match substitutions with
  | [] => value
  | (replacement, y) :: rest => substitute_values rest (subst_val_valu replacement y value)
  end.
Lemma read_symbol_ground_substitutions x pattern actual substitutions found :
  read_symbol x pattern actual = Some found ->
  base_ground found ->
  read_symbol x pattern (substitute_values substitutions actual) = Some found.
Proof.
  revert actual. induction substitutions as [|[replacement y] rest IH]; intros actual Hread Hground;
    simpl; [exact Hread|].
  apply IH; [eapply read_symbol_ground_substitution; eassumption|exact Hground].
Qed.
Print Assumptions base_ground_reflect.
Print Assumptions base_ground_substitution.
Print Assumptions read_symbol_ground_substitution.
Print Assumptions read_symbol_ground_substitutions.

Lemma read_accessor_pins x replacement al pattern pattern' actual' found :
  read_accessor al pattern = Some pattern' ->
  read_accessor al (subst_val_valu replacement x pattern) = Some actual' ->
  read_symbol x pattern' actual' = Some found ->
  found = replacement.
Proof.
  intros Hpattern Hactual Hread.
  rewrite read_accessor_substitution Hpattern in Hactual. simpl in Hactual.
  injection Hactual as Heq. rewrite <-Heq in Hread.
  exact (read_symbol_substitution x pattern' replacement found Hread).
Qed.
Print Assumptions read_accessor_pins.

(** A pending register read fixes the declaration witness before any write. *)
Definition event_writesb (e : event) : bool :=
  match e with WriteReg _ _ _ _ | WriteMem _ _ _ _ _ _ _ => true | _ => false end.
Lemma event_writesb_substitution e replacement y :
  event_writesb (subst_val_event replacement y e) = event_writesb e.
Proof. destruct e; try destruct smt5; reflexivity. Qed.

Inductive RegisterReadPin (x : var_name) (marker : valu)
    (predicted pinned : base_val) (regs : reg_map) : isla_trace -> Prop :=
| RegisterReadPinHere name al pattern ann rest actual actualValue patternValue :
    regs !! name = Some actual ->
    read_accessor al actual = Some actualValue ->
    read_accessor al pattern = Some patternValue ->
    read_symbol x marker actualValue = Some pinned ->
    read_symbol x marker patternValue = Some predicted ->
    RegisterReadPin x marker predicted pinned regs (ReadReg name al pattern ann :t: rest)
| RegisterReadPinLater e rest :
    event_writesb e = false ->
    RegisterReadPin x marker predicted pinned regs rest ->
    RegisterReadPin x marker predicted pinned regs (e :t: rest).

Lemma register_read_pin_substitution x marker predicted pinned regs trace replacement y :
  RegisterReadPin x marker predicted pinned regs trace ->
  base_ground predicted ->
  RegisterReadPin x marker predicted pinned regs (subst_trace replacement y trace).
Proof.
  intros Hpin Hground. induction Hpin; simpl.
  - eapply RegisterReadPinHere with
      (actual := actual) (actualValue := actualValue)
      (patternValue := subst_val_valu replacement y patternValue); try eassumption.
    + rewrite read_accessor_substitution H1. reflexivity.
    + eapply read_symbol_ground_substitution; eassumption.
  - apply RegisterReadPinLater; [rewrite event_writesb_substitution; assumption|assumption].
Qed.
Print Assumptions register_read_pin_substitution.

Lemma seq_event_no_write e rest theta sigma labels theta' sigma' :
  seq_trace theta = e :t: rest ->
  event_writesb e = false ->
  seq_step theta sigma labels theta' sigma' [] ->
  sigma' = sigma /\ seq_regs theta' = seq_regs theta /\ seq_pc_reg theta' = seq_pc_reg theta.
Proof.
  intros Htrace Hw Hstep. inversion Hstep; subst.
  match goal with H : trace_step _ _ _ _ |- _ => rewrite Htrace in H; inversion H; subst end.
  all: simpl in Hw; try discriminate.
  all: simpl in *.
  all: repeat match goal with
    | H : exists _, _ |- _ => destruct H as [? H]
    | H : _ /\ _ |- _ => destruct H as [? ?]
    end.
  all: try match goal with H : context [read_mem ?mem ?address ?len] |- _ =>
    destruct (read_mem mem address len) eqn:Hread; simpl in H end.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  all: repeat match goal with H : _ \/ _ |- _ => destruct H end.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  all: subst; repeat split; reflexivity.
Qed.
Print Assumptions seq_event_no_write.

Lemma seq_step_keeps_trace theta sigma labels theta' sigma' :
  seq_step theta sigma labels theta' sigma' [] ->
  seq_nb_state theta' = false ->
  exists label next,
    trace_step (seq_trace theta) (seq_regs theta) label next /\ seq_trace theta' = next.
Proof.
  intros Hstep Hnb. inversion Hstep; subst.
  eexists; eexists. split; [eassumption|].
  match goal with H : match ?label with _ => _ end |- _ => destruct label as [label|];
    [destruct label|]; simpl in H end.
  all: repeat match goal with
    | H : exists _, _ |- _ => destruct H as [? H]
    | H : _ /\ _ |- _ => destruct H as [? ?]
    end.
  all: try match goal with H : context [read_mem ?mem ?address ?len] |- _ =>
    destruct (read_mem mem address len) eqn:Hread; simpl in H end.
  all: try match goal with H : context [seq_instrs ?sigma !! ?pc] |- _ =>
    destruct (seq_instrs sigma !! pc) eqn:Hinstr; simpl in H end.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  all: repeat match goal with H : _ \/ _ |- _ => destruct H end.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  all: subst; simpl in *; try discriminate; reflexivity.
Qed.
Print Assumptions seq_step_keeps_trace.

Lemma trace_cons_step_forms e rest regs label next :
  trace_step (e :t: rest) regs label next ->
  (exists replacement y, next = subst_trace replacement y rest) \/ next = rest.
Proof. intros Hstep. inversion Hstep; subst; eauto 6. Qed.
Lemma seq_read_register_equal name al pattern ann rest theta sigma labels theta' sigma' :
  seq_trace theta = ReadReg name al pattern ann :t: rest ->
  seq_step theta sigma labels theta' sigma' [] ->
  seq_nb_state theta' = false ->
  exists actual value,
    seq_regs theta !! name = Some actual /\
    read_accessor al actual = Some value /\ read_accessor al pattern = Some value.
Proof.
  intros Htrace Hstep Hnb. inversion Hstep; subst.
  match goal with H : trace_step _ _ _ _ |- _ => rewrite Htrace in H; inversion H; subst end.
  simpl in *.
  repeat match goal with
  | H : exists _, _ |- _ => destruct H as [? H]
  | H : _ /\ _ |- _ => destruct H as [? ?]
  end.
  match goal with H : _ \/ _ |- _ => destruct H end.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  all: subst; simpl in Hnb; try discriminate; eauto 6.
Qed.
Print Assumptions trace_cons_step_forms.
Print Assumptions seq_read_register_equal.

Lemma register_read_pin_step x marker predicted pinned regs trace theta sigma labels theta' sigma' :
  RegisterReadPin x marker predicted pinned regs trace ->
  base_ground predicted ->
  seq_trace theta = trace ->
  seq_regs theta = regs ->
  seq_step theta sigma labels theta' sigma' [] ->
  seq_nb_state theta' = false ->
  predicted = pinned \/
  RegisterReadPin x marker predicted pinned (seq_regs theta') (seq_trace theta').
Proof.
  intros Hpin Hground Htrace Hregs Hstep Hnb.
  destruct Hpin as [name al pattern ann rest actual actualValue patternValue
      Hreg Hactual Hpattern Hpinned Hpredicted|e rest Hw Htail].
  - left.
    destruct (seq_read_register_equal name al pattern ann rest theta sigma labels theta' sigma'
      Htrace Hstep Hnb) as [actual' [value [Hreg' [Hactual' Hpattern']]]].
    rewrite Hregs in Hreg'.
    assert (actual = actual') by congruence. subst actual'.
    assert (actualValue = value) by congruence.
    assert (patternValue = value) by congruence.
    congruence.
  - right.
    destruct (seq_step_keeps_trace theta sigma labels theta' sigma' Hstep Hnb)
      as [label [next [HtraceStep Hnext]]].
    destruct (seq_event_no_write e rest theta sigma labels theta' sigma' Htrace Hw Hstep)
      as [_ [Hregs' _]].
    rewrite Htrace Hregs in HtraceStep.
    destruct (trace_cons_step_forms e rest regs label next HtraceStep)
      as [[replacement [y Hform]]|Hform].
    + rewrite Hregs' Hregs Hnext Hform.
      eapply register_read_pin_substitution; eassumption.
    + rewrite Hregs' Hregs Hnext Hform. exact Htail.
Qed.
Print Assumptions register_read_pin_step.

Lemma register_read_pin_prefix n theta sigma labels theta' sigma' x marker predicted pinned :
  InstructionPrefix n theta sigma labels theta' sigma' ->
  RegisterReadPin x marker predicted pinned (seq_regs theta) (seq_trace theta) ->
  base_ground predicted ->
  seq_trace theta' = tnil ->
  predicted = pinned.
Proof.
  intros Hprefix. induction Hprefix; intros Hpin Hground Hnil.
  - rewrite Hnil in Hpin. inversion Hpin.
  - destruct (register_read_pin_step x marker predicted pinned (seq_regs theta)
      (seq_trace theta) theta sigma labels theta' sigma' Hpin Hground eq_refl eq_refl H0 H1)
      as [Heq|Hnext]; [exact Heq|].
    eapply IHHprefix; eassumption.
Qed.
Lemma register_read_pin_completed theta sigma labels theta' sigma' x marker predicted pinned :
  CompletedInstructionSegment theta sigma labels theta' sigma' ->
  RegisterReadPin x marker predicted pinned (seq_regs theta) (seq_trace theta) ->
  base_ground predicted ->
  predicted = pinned.
Proof.
  intros [n [boundary [memory [prefix [last [Hprefix [Hnil _]]]]]]] Hpin Hground.
  eapply register_read_pin_prefix; eassumption.
Qed.
Print Assumptions register_read_pin_prefix.
Print Assumptions register_read_pin_completed.

(** Complementary leading assertions select at most one completed branch. *)
Local Instance bvarith_eq_dec : EqDecision bvarith.
Proof. solve_decision. Defined.
Local Instance bvcomp_eq_dec : EqDecision bvcomp.
Proof. solve_decision. Defined.
Local Instance bvmanyarith_eq_dec : EqDecision bvmanyarith.
Proof. solve_decision. Defined.
Local Instance unop_eq_dec : EqDecision unop.
Proof. solve_decision. Defined.
Local Instance binop_eq_dec : EqDecision binop.
Proof. solve_decision. Defined.
Local Instance manyop_eq_dec : EqDecision manyop.
Proof. solve_decision. Defined.
Fixpoint expression_sameb (left right : exp) {struct left} : bool :=
  match left, right with
  | Val x _, Val y _ => executor_base_eqb x y
  | Unop op x _, Unop op' y _ => bool_decide (op = op') && expression_sameb x y
  | Binop op x z _, Binop op' y w _ =>
      bool_decide (op = op') && expression_sameb x y && expression_sameb z w
  | Manyop op xs _, Manyop op' ys _ =>
      bool_decide (op = op') &&
      (let fix go xs ys :=
        match xs, ys with
        | [], [] => true
        | x :: xs', y :: ys' => expression_sameb x y && go xs' ys'
        | _, _ => false
        end in go xs ys)
  | Ite x z u _, Ite y w v _ =>
      expression_sameb x y && expression_sameb z w && expression_sameb u v
  | _, _ => false
  end.
Lemma expression_sameb_reflect left right : expression_sameb left right = true <-> left = right.
Proof.
  revert left right. fix IH 1. intros left right.
  destruct left; destruct right; simpl; try (split; [discriminate|congruence]);
    repeat match goal with a : annot |- _ => destruct a end.
  - rewrite executor_base_eqb_reflect. split; congruence.
  - rewrite andb_true_iff bool_decide_eq_true (IH left right). split; intros; intuition congruence.
  - rewrite !andb_true_iff bool_decide_eq_true (IH left1 right1) (IH left2 right2).
    split; intros; intuition congruence.
  - rewrite andb_true_iff bool_decide_eq_true.
    assert (Hlists : (let fix go xs ys :=
        match xs, ys with
        | [], [] => true
        | x :: xs', y :: ys' => expression_sameb x y && go xs' ys'
        | _, _ => false end in go l l0) = true <-> l = l0).
    { revert l0. induction l as [|x xs IHlist]; intros [|y ys]; simpl;
        try (split; [discriminate|congruence]); [split; congruence|].
      rewrite andb_true_iff (IH x y) IHlist. split; intros; intuition congruence. }
    rewrite Hlists. split; intros; intuition congruence.
  - rewrite !andb_true_iff (IH left1 right1) (IH left2 right2) (IH left3 right3).
    split; intros; intuition congruence.
Qed.
Print Assumptions expression_sameb_reflect.
Definition negated_assertion_pairb (positive negative : isla_trace) : bool :=
  match positive, negative with
  | Smt (Assert e) _ :t: _, Smt (Assert (Unop Not e' _)) _ :t: _ => expression_sameb e e'
  | _, _ => false
  end.
Definition negated_assertion_pair (positive negative : isla_trace) : Prop :=
  match positive, negative with
  | Smt (Assert e) _ :t: _, Smt (Assert (Unop Not e' _)) _ :t: _ => e = e'
  | _, _ => False
  end.
Lemma negated_assertion_pair_reflect positive negative :
  negated_assertion_pairb positive negative = true <-> negated_assertion_pair positive negative.
Proof.
  unfold negated_assertion_pairb, negated_assertion_pair.
  destruct positive; destruct negative; simpl; try (split; [discriminate|contradiction]).
  all: repeat match goal with v : event |- _ => destruct v end; simpl;
    try (split; [discriminate|contradiction]).
  all: repeat match goal with v : smt |- _ => destruct v end; simpl;
    try (split; [discriminate|contradiction]).
  destruct exp5; simpl; try (split; [discriminate|contradiction]).
  destruct unop5; simpl; try (split; [discriminate|contradiction]).
  apply expression_sameb_reflect.
Qed.
Definition complementary_assertionsb left right : bool :=
  negated_assertion_pairb left right || negated_assertion_pairb right left.
Definition complementary_assertions left right : Prop :=
  negated_assertion_pair left right \/ negated_assertion_pair right left.
Lemma complementary_assertions_reflect left right :
  complementary_assertionsb left right = true <-> complementary_assertions left right.
Proof. unfold complementary_assertionsb, complementary_assertions.
  rewrite orb_true_iff !negated_assertion_pair_reflect. reflexivity. Qed.
Definition branches_exclusiveb branches : bool :=
  match branches with
  | [] | [_] => true
  | [first; second] => complementary_assertionsb first second
  | _ => false
  end.
Definition branches_exclusive branches : Prop :=
  match branches with
  | [] | [_] => True
  | [first; second] => complementary_assertions first second
  | _ => False
  end.
Lemma branches_exclusive_reflect branches :
  branches_exclusiveb branches = true <-> branches_exclusive branches.
Proof.
  destruct branches as [|left [|right [|third rest]]]; simpl;
    try tauto; try (split; [discriminate|contradiction]).
  apply complementary_assertions_reflect.
Qed.
Fixpoint trace_exclusiveb trace : bool :=
  match trace with
  | tnil => true
  | _ :t: rest => trace_exclusiveb rest
  | tcases branches => branches_exclusiveb branches && forallb trace_exclusiveb branches
  end.
Fixpoint trace_exclusive trace : Prop :=
  match trace with
  | tnil => True
  | _ :t: rest => trace_exclusive rest
  | tcases branches => branches_exclusive branches /\
      (let fix go branches := match branches with
        | [] => True | branch :: rest => trace_exclusive branch /\ go rest end in go branches)
  end.
Lemma trace_exclusive_reflect trace : trace_exclusiveb trace = true <-> trace_exclusive trace.
Proof.
  revert trace. fix IH 1. intros [|event rest|branches]; simpl; [tauto|apply IH|].
  rewrite andb_true_iff branches_exclusive_reflect.
  assert (Hbranches : forallb trace_exclusiveb branches = true <->
    (let fix go branches := match branches with
      | [] => True | branch :: rest => trace_exclusive branch /\ go rest end in go branches)).
  { induction branches as [|branch rest IHlist]; simpl; [tauto|].
    rewrite andb_true_iff (IH branch) IHlist. reflexivity. }
  rewrite Hbranches. reflexivity.
Qed.
Print Assumptions negated_assertion_pair_reflect.
Print Assumptions complementary_assertions_reflect.
Print Assumptions branches_exclusive_reflect.
Print Assumptions trace_exclusive_reflect.
Lemma negated_assertion_pair_substitution positive negative replacement x :
  negated_assertion_pair positive negative ->
  negated_assertion_pair (subst_trace replacement x positive) (subst_trace replacement x negative).
Proof.
  unfold negated_assertion_pair.
  destruct positive; destruct negative; simpl; try tauto.
  all: repeat match goal with v : event |- _ => destruct v end; simpl; try tauto.
  all: repeat match goal with v : smt |- _ => destruct v end; simpl; try tauto.
  destruct exp5; simpl; try tauto. destruct unop5; simpl; try tauto.
  intros ->. reflexivity.
Qed.
Lemma complementary_assertions_substitution first second replacement x :
  complementary_assertions first second ->
  complementary_assertions (subst_trace replacement x first) (subst_trace replacement x second).
Proof.
  unfold complementary_assertions. intros [Hpair|Hpair];
    [left|right]; apply negated_assertion_pair_substitution; exact Hpair.
Qed.
Lemma branches_exclusive_substitution branches replacement x :
  branches_exclusive branches -> branches_exclusive (subst_trace replacement x <$> branches).
Proof.
  destruct branches as [|first [|second [|third rest]]]; simpl; try tauto.
  apply complementary_assertions_substitution.
Qed.
Lemma trace_exclusive_substitution trace replacement x :
  trace_exclusive trace -> trace_exclusive (subst_trace replacement x trace).
Proof.
  revert trace. fix IH 1. intros [|event rest|branches]; simpl; [tauto|apply IH|].
  intros [Hshape Hall]. split; [apply branches_exclusive_substitution; exact Hshape|].
  clear Hshape. induction branches as [|branch rest IHlist]; simpl in *; [tauto|].
  destruct Hall as [Hbranch Hrest]. split; [apply IH; exact Hbranch|apply IHlist; exact Hrest].
Qed.
Print Assumptions negated_assertion_pair_substitution.
Print Assumptions complementary_assertions_substitution.
Print Assumptions branches_exclusive_substitution.
Print Assumptions trace_exclusive_substitution.

(** A completed branch passes its leading assertion. *)
Lemma seq_assert_eval_true expression ann rest theta sigma labels theta' sigma' :
  seq_trace theta = Smt (Assert expression) ann :t: rest ->
  seq_step theta sigma labels theta' sigma' [] ->
  seq_nb_state theta' = false ->
  eval_exp expression = Some (Val_Bool true).
Proof.
  intros Htrace Hstep Hnb. inversion Hstep; subst.
  match goal with H : trace_step _ _ _ _ |- _ => rewrite Htrace in H; inversion H; subst end.
  simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  subst. simpl in Hnb. destruct b; [assumption|discriminate].
Qed.
Print Assumptions seq_assert_eval_true.
Lemma completed_assert_eval_true expression ann rest regs sigma labels theta' sigma' :
  CompletedInstructionSegment
    (instruction_boundary (Smt (Assert expression) ann :t: rest) regs)
    sigma labels theta' sigma' ->
  eval_exp expression = Some (Val_Bool true).
Proof.
  intros [n [boundary [memory [prefix [last [Hprefix [Hnil _]]]]]]].
  inversion Hprefix; subst.
  - discriminate Hnil.
  - eapply seq_assert_eval_true with (theta := instruction_boundary (Smt (Assert expression) ann :t: rest) regs); [reflexivity|eassumption|eassumption].
Qed.
Print Assumptions completed_assert_eval_true.
Lemma negated_assertions_not_both expression ann :
  eval_exp expression = Some (Val_Bool true) ->
  eval_exp (Unop Not expression ann) <> Some (Val_Bool true).
Proof. simpl. intros ->. discriminate. Qed.
Print Assumptions negated_assertions_not_both.

Lemma negated_assertion_pair_not_both first second regs sigma
    labels theta' sigma' labels' theta'' sigma'' :
  negated_assertion_pair first second ->
  ~ (CompletedInstructionSegment (instruction_boundary first regs) sigma labels theta' sigma' /\
     CompletedInstructionSegment (instruction_boundary second regs) sigma labels' theta'' sigma'').
Proof.
  unfold negated_assertion_pair.
  destruct first; destruct second; simpl; try tauto.
  all: repeat match goal with v : event |- _ => destruct v end; simpl; try tauto.
  all: repeat match goal with v : smt |- _ => destruct v end; simpl; try tauto.
  destruct exp5; simpl; try tauto. destruct unop5; simpl; try tauto.
  intros Heq [Hfirst Hsecond]. subst exp5.
  apply completed_assert_eval_true in Hfirst. apply completed_assert_eval_true in Hsecond.
  simpl in Hsecond. rewrite Hfirst in Hsecond. discriminate.
Qed.
Lemma complementary_assertions_not_both first second regs sigma
    labels theta' sigma' labels' theta'' sigma'' :
  complementary_assertions first second ->
  ~ (CompletedInstructionSegment (instruction_boundary first regs) sigma labels theta' sigma' /\
     CompletedInstructionSegment (instruction_boundary second regs) sigma labels' theta'' sigma'').
Proof.
  intros [Hpair|Hpair] [Hfirst Hsecond].
  - eapply negated_assertion_pair_not_both; [exact Hpair|split; eassumption].
  - eapply negated_assertion_pair_not_both; [exact Hpair|split; eassumption].
Qed.
Print Assumptions negated_assertion_pair_not_both.
Print Assumptions complementary_assertions_not_both.
Lemma branches_exclusive_completed_unique branches branch branch' regs sigma
    labels theta' sigma' labels' theta'' sigma'' :
  branches_exclusive branches -> branch ∈ branches -> branch' ∈ branches ->
  CompletedInstructionSegment (instruction_boundary branch regs) sigma labels theta' sigma' ->
  CompletedInstructionSegment (instruction_boundary branch' regs) sigma labels' theta'' sigma'' ->
  branch = branch'.
Proof.
  destruct branches as [|first [|second [|third rest]]]; simpl;
    intros Hshape Hmember Hmember' Hrun Hrun'.
  - set_solver.
  - set_solver.
  - assert (Hfirst : branch = first \/ branch = second) by set_solver.
    assert (Hsecond : branch' = first \/ branch' = second) by set_solver.
    destruct Hfirst as [-> | ->]; destruct Hsecond as [-> | ->]; try reflexivity.
    + exfalso. eapply complementary_assertions_not_both; [exact Hshape|split; eassumption].
    + exfalso. eapply complementary_assertions_not_both; [exact Hshape|split; eassumption].
  - contradiction.
Qed.
Print Assumptions branches_exclusive_completed_unique.

Lemma rval_bv_injective n (x y : bv n) : RVal_Bits x = RVal_Bits y -> x = y.
Proof.
  intros H. apply bv_eq.
  apply (f_equal (fun value => match value with RVal_Bits bits => bvn_unsigned bits | _ => 0 end)) in H.
  exact H.
Qed.
Lemma seq_nondeclaration_unique event rest theta sigma labels theta' sigma' labels' theta'' sigma'' :
  seq_trace theta = event :t: rest -> event_declares event = false ->
  seq_step theta sigma labels theta' sigma' [] -> seq_nb_state theta' = false ->
  seq_step theta sigma labels' theta'' sigma'' [] -> seq_nb_state theta'' = false ->
  labels = labels' /\ theta' = theta'' /\ sigma' = sigma''.
Proof.
  intros Htrace Hdecl Hstep Hnb Hstep' Hnb'.
  inversion Hstep; subst. inversion Hstep'; subst.
  match goal with
  | Hfirst : trace_step (seq_trace theta) (seq_regs theta) ?label ?next,
    Hsecond : trace_step (seq_trace theta) (seq_regs theta) ?label' ?next' |- _ =>
      rewrite Htrace in Hfirst, Hsecond;
      pose proof (trace_event_deterministic event rest (seq_regs theta)
        label next label' next' Hdecl Hfirst Hsecond) as [Hlabel Hnext];
      subst label' next'
  end.
  destruct κ as [label|]; [destruct label|]; simpl in *;
    repeat match goal with
    | H : exists _, _ |- _ => destruct H as [? H]
    | H : _ /\ _ |- _ => destruct H as [? ?]
    | H : _ \/ _ |- _ => destruct H
    end; subst; simpl in *; try discriminate; try (repeat split; congruence).
  all: try solve [match goal with H : trace_step _ _ _ _ |- _ => inversion H; subst; congruence end].
  all: repeat match goal with
    | H : RegVal_Base (Val_Bits (@bv_to_bvn ?n ?x)) = RegVal_Base (Val_Bits (@bv_to_bvn ?n ?y)) |- _ =>
        apply (rval_bv_injective n x y) in H; subst
    end.
  all: repeat match goal with
    | H : context [match ?value with Some _ => _ | None => _ end] |- _ =>
        destruct value eqn:?; simpl in H
    | H : _ /\ _ |- _ => destruct H as [? ?]
    | H : _ \/ _ |- _ => destruct H
    end; subst; simpl in *; try discriminate; try (repeat split; congruence).
Qed.

Print Assumptions seq_nondeclaration_unique.

Lemma completed_cons_invert event rest theta sigma labels theta' sigma' :
  seq_trace theta = event :t: rest ->
  CompletedInstructionSegment theta sigma labels theta' sigma' ->
  exists first theta1 sigma1 tail,
    seq_step theta sigma first theta1 sigma1 [] /\
    seq_nb_state theta1 = false /\
    CompletedInstructionSegment theta1 sigma1 tail theta' sigma' /\
    labels = first ++ tail.
Proof.
  intros Htrace [n [boundary [memory [prefix [last [Hprefix [Hnil [Hlast Hlabels]]]]]]]].
  inversion Hprefix; subst.
  - rewrite Htrace in Hnil. discriminate.
  - exists labels0, theta'0, sigma'0, (tail ++ last).
    split; [exact H0|]. split; [exact H1|]. split.
    + exists n0, boundary, memory, tail, last. repeat split; assumption.
    + symmetry. apply app_assoc.
Qed.
Print Assumptions completed_cons_invert.
Lemma seq_step_preserves_pc theta sigma labels theta' sigma' :
  seq_step theta sigma labels theta' sigma' [] -> seq_pc_reg theta' = seq_pc_reg theta.
Proof.
  intros Hstep. inversion Hstep; subst; simpl in *.
  destruct κ as [label|]; [destruct label|]; simpl in *;
    repeat match goal with
    | H : exists _, _ |- _ => destruct H as [? H]
    | H : _ /\ _ |- _ => destruct H as [? ?]
    | H : _ \/ _ |- _ => destruct H
    end; subst; simpl; try reflexivity.
  all: repeat match goal with
    | H : context [match ?value with Some _ => _ | None => _ end] |- _ =>
        destruct value eqn:?; simpl in H
    | H : _ /\ _ |- _ => destruct H as [? ?]
    | H : _ \/ _ |- _ => destruct H
    end; subst; simpl; reflexivity.
Qed.
Print Assumptions seq_step_preserves_pc.
Lemma seq_boundary_canonical trace regs sigma labels theta' sigma' :
  seq_step (instruction_boundary trace regs) sigma labels theta' sigma' [] ->
  seq_nb_state theta' = false ->
  theta' = instruction_boundary (seq_trace theta') (seq_regs theta').
Proof.
  intros Hstep Hnb. pose proof (seq_step_preserves_pc _ _ _ _ _ Hstep) as Hpc.
  destruct theta' as [trace' regs' pc' nb']; simpl in *.
  subst pc' nb'. reflexivity.
Qed.
Print Assumptions seq_boundary_canonical.
Lemma completed_nonterminal_invert theta sigma labels theta' sigma' :
  seq_trace theta <> tnil ->
  CompletedInstructionSegment theta sigma labels theta' sigma' ->
  exists first theta1 sigma1 tail,
    seq_step theta sigma first theta1 sigma1 [] /\
    seq_nb_state theta1 = false /\
    CompletedInstructionSegment theta1 sigma1 tail theta' sigma' /\
    labels = first ++ tail.
Proof.
  intros Htrace [n [boundary [memory [prefix [last [Hprefix [Hnil [Hlast Hlabels]]]]]]]].
  inversion Hprefix; subst.
  - contradiction.
  - exists labels0, theta'0, sigma'0, (tail ++ last).
    split; [exact H0|]. split; [exact H1|]. split.
    + exists n0, boundary, memory, tail, last. repeat split; assumption.
    + symmetry. apply app_assoc.
Qed.
Print Assumptions completed_nonterminal_invert.
Lemma seq_cases_step branches theta sigma labels theta' sigma' :
  seq_trace theta = tcases branches ->
  seq_step theta sigma labels theta' sigma' [] ->
  exists branch, branch ∈ branches /\ labels = [] /\
    theta' = theta <| seq_trace := branch |> /\ sigma' = sigma.
Proof.
  intros Htrace Hstep. inversion Hstep; subst.
  match goal with H : trace_step _ _ _ _ |- _ => rewrite Htrace in H; inversion H; subst end.
  simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  subst. eexists. repeat split; eassumption.
Qed.
Print Assumptions seq_cases_step.
Lemma completed_cases_invert branches regs sigma labels theta' sigma' :
  CompletedInstructionSegment (instruction_boundary (tcases branches) regs)
    sigma labels theta' sigma' ->
  exists branch, branch ∈ branches /\
    CompletedInstructionSegment (instruction_boundary branch regs)
      sigma labels theta' sigma'.
Proof.
  intros Hrun.
  destruct (completed_nonterminal_invert (instruction_boundary (tcases branches) regs) sigma labels theta' sigma' ltac:(discriminate) Hrun)
    as (first & theta1 & sigma1 & tail & Hstep & Hnb & Htail & Hlabels).
  destruct (seq_cases_step branches (instruction_boundary (tcases branches) regs) sigma first theta1 sigma1 eq_refl Hstep)
    as (branch & Hmember & Hfirst & Htheta & Hsigma).
  subst first theta1 sigma1. simpl in Hlabels. subst tail.
  exists branch. split; [exact Hmember|exact Htail].
Qed.
Print Assumptions completed_cases_invert.
Definition DeclarationValue ty replacement : Prop :=
  match ty with
  | Ty_Bool => exists value : bool, replacement = Val_Bool value
  | Ty_BitVec n => exists value : bv n, replacement = Val_Bits value
  | Ty_Enum _ => exists value : string, replacement = Val_Enum value
  | _ => False
  end.
Lemma seq_declaration_step x ty ann rest theta sigma labels theta' sigma' :
  seq_trace theta = Smt (DeclareConst x ty) ann :t: rest ->
  seq_step theta sigma labels theta' sigma' [] ->
  exists replacement, DeclarationValue ty replacement /\ labels = [] /\
    theta' = theta <| seq_trace := subst_trace replacement x rest |> /\ sigma' = sigma.
Proof.
  intros Htrace Hstep. inversion Hstep; subst.
  match goal with H : trace_step _ _ _ _ |- _ => rewrite Htrace in H; inversion H; subst end.
  all: simpl in *; repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  all: subst; eexists; repeat split; try reflexivity.
  all: unfold DeclarationValue; eexists; reflexivity.
Qed.
Print Assumptions seq_declaration_step.
Lemma declaration_value_ground ty replacement : DeclarationValue ty replacement -> base_ground replacement.
Proof. destruct ty; simpl; try contradiction; intros [value ->]; exact I. Qed.
Print Assumptions declaration_value_ground.
Lemma completed_declaration_invert x ty ann rest regs sigma labels theta' sigma' :
  CompletedInstructionSegment
    (instruction_boundary (Smt (DeclareConst x ty) ann :t: rest) regs)
    sigma labels theta' sigma' ->
  exists replacement, DeclarationValue ty replacement /\
    CompletedInstructionSegment (instruction_boundary (subst_trace replacement x rest) regs)
      sigma labels theta' sigma'.
Proof.
  intros Hrun.
  destruct (completed_nonterminal_invert
      (instruction_boundary (Smt (DeclareConst x ty) ann :t: rest) regs)
      sigma labels theta' sigma' ltac:(discriminate) Hrun)
    as (first & theta1 & sigma1 & tail & Hstep & Hnb & Htail & Hlabels).
  destruct (seq_declaration_step x ty ann rest
      (instruction_boundary (Smt (DeclareConst x ty) ann :t: rest) regs)
      sigma first theta1 sigma1 eq_refl Hstep)
    as (replacement & Hvalue & Hfirst & Htheta & Hsigma).
  subst first theta1 sigma1. simpl in Hlabels. subst tail.
  exists replacement. split; [exact Hvalue|exact Htail].
Qed.
Print Assumptions completed_declaration_invert.
Lemma exec_declaration_matches_value x ty rest regs sigma replacement :
  DeclarationValue ty replacement ->
  declaration_read (isla_trace_length rest) x rest regs sigma = Some replacement ->
  exec_declaration x ty rest regs sigma = Some (subst_trace replacement x rest).
Proof.
  destruct ty; simpl; try contradiction; intros [value ->] Hread;
    unfold exec_declaration; rewrite Hread; simpl; try reflexivity.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Print Assumptions exec_declaration_matches_value.
Lemma exec_declaration_unused x ty rest regs sigma next :
  trace_unused x rest -> exec_declaration x ty rest regs sigma = Some next -> next = rest.
Proof.
  intros Hunused. apply trace_unused_reflect in Hunused. unfold exec_declaration. destruct ty; try discriminate;
    intros [= <-]; apply trace_unused_substitution; exact Hunused.
Qed.
Print Assumptions exec_declaration_unused.

Lemma exec_register_conditions event regs sigma regs' sigma' labels conditions :
  exec_register_event event regs sigma = Some (regs', sigma', labels, conditions) ->
  exec_event_feasibleb event regs sigma = true -> ExecutorConditions conditions.
Proof.
  destruct event; simpl; try discriminate.
  - destruct (regs !! name5) as [actual|] eqn:Hactual; simpl; [|discriminate].
    destruct (read_accessor accessor_list5 actual) as [value|] eqn:Hvalue; simpl; [|discriminate].
    destruct (read_accessor accessor_list5 valu5) as [pattern|] eqn:Hpattern; simpl; [|discriminate].
    intros [= <- <- <- <-] Hguard. apply executor_valu_eqb_reflect in Hguard.
    unfold ExecutorConditions. repeat constructor. congruence.
  - destruct (regs !! name5) as [actual|]; simpl; [|discriminate].
    destruct (read_accessor accessor_list5 valu5) as [value|]; simpl; [|discriminate].
    destruct (write_accessor accessor_list5 actual value); simpl; [|discriminate].
    intros [= <- <- <- <-] _. constructor.
  - destruct (regs !! name5) as [actual|]; simpl; [|discriminate].
    intros [= <- <- <- <-] Hguard. apply executor_option_valu_eqb_reflect in Hguard.
    unfold ExecutorConditions. repeat constructor. exact Hguard.
Qed.
Print Assumptions exec_register_conditions.
Lemma exec_silent_conditions event rest regs sigma next regs' sigma' labels conditions :
  exec_silent_event event rest regs sigma = Some (next, (regs', sigma', labels, conditions)) ->
  ExecutorConditions conditions.
Proof.
  destruct event; try destruct smt5; simpl; try discriminate.
  all: repeat match goal with
    | |- context [eval_exp ?expression] => destruct (eval_exp expression) eqn:?; simpl
    | |- context [eval_a_exp ?regs ?expression] => destruct (eval_a_exp regs expression) eqn:?; simpl
    | value : base_val |- _ => destruct value; simpl
    | value : bool |- _ => destruct value; simpl
    end; try discriminate; intros Heq; inversion Heq; subst;
    unfold ExecutorConditions; repeat constructor.
Qed.
Print Assumptions exec_silent_conditions.
Lemma exec_memory_conditions event regs sigma regs' sigma' labels conditions :
  exec_memory_event event regs sigma = Some (regs', sigma', labels, conditions) ->
  exec_event_feasibleb event regs sigma = true -> ExecutorConditions conditions.
Proof.
  destruct event; simpl; try discriminate.
  - destruct addr; try discriminate. destruct base_val5; try discriminate.
    destruct valu5; try discriminate. destruct base_val5; try discriminate.
    destruct (read_mem (seq_mem sigma) (bv_unsigned (Z_to_bv 64 (bvn_unsigned bv5))) num_bytes)
      as [memory|] eqn:Hmemory; simpl; [|discriminate].
    intros Heq Hguard. inversion Heq; subst.
    repeat match goal with
    | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
    | H : executor_bits_eqb _ _ = true |- _ => apply executor_bits_eqb_reflect in H
    | H : bool_decide _ = true |- _ => apply bool_decide_eq_true in H
    end.
    unfold ExecutorConditions. repeat constructor; try assumption; congruence.
  - destruct addr; try discriminate. destruct base_val5; try discriminate.
    destruct data; try discriminate. destruct base_val5; try discriminate.
    destruct (read_mem (seq_mem sigma) (bv_unsigned (Z_to_bv 64 (bvn_unsigned bv5))) num_bytes)
      as [memory|] eqn:Hmemory; simpl; intros Heq Hguard; inversion Heq; subst;
    repeat match goal with
    | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
    | H : executor_bits_eqb _ _ = true |- _ => apply executor_bits_eqb_reflect in H
    | H : bool_decide _ = true |- _ => apply bool_decide_eq_true in H
    | H : executor_write_disjointb _ _ _ = true |- _ => apply executor_write_disjointb_reflect in H
    end; unfold ExecutorConditions; repeat constructor; try assumption; congruence.
Qed.
Print Assumptions exec_memory_conditions.
Lemma exec_nondeclaration_conditions event rest regs sigma next regs' sigma' labels conditions :
  exec_nondeclaration_event event rest regs sigma = Some (next, (regs', sigma', labels, conditions)) ->
  ExecutorConditions conditions.
Proof.
  unfold exec_nondeclaration_event.
  destruct (exec_event_feasibleb event regs sigma) eqn:Hguard; [|discriminate].
  destruct (exec_silent_event event rest regs sigma) as [result|] eqn:Hsilent.
  - intros Heq. inversion Heq; subst result. eapply exec_silent_conditions; exact Hsilent.
  - destruct (exec_register_event event regs sigma) as [result|] eqn:Hregister.
    + intros Heq. inversion Heq; subst result. eapply exec_register_conditions; [exact Hregister|exact Hguard].
    + destruct (exec_memory_event event regs sigma) as [result|] eqn:Hmemory; simpl; [|discriminate].
      intros Heq. inversion Heq; subst result. eapply exec_memory_conditions; [exact Hmemory|exact Hguard].
Qed.
Print Assumptions exec_nondeclaration_conditions.
Lemma exec_event_success_conditions event rest regs sigma next regs' sigma' labels conditions :
  exec_event event rest regs sigma = Some (next, (regs', sigma', labels, conditions)) ->
  ExecutorConditions conditions.
Proof.
  destruct event; try destruct smt5; cbn [exec_event]; try apply exec_nondeclaration_conditions.
  destruct (exec_declaration vvar5 ty5 rest regs sigma); simpl; [|discriminate].
  intros Heq. inversion Heq; subst. constructor.
Qed.
Print Assumptions exec_event_success_conditions.
Lemma exec_trace_success_conditions fuel trace regs sigma regs' sigma' labels conditions :
  exec_trace fuel trace regs sigma = Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions.
Proof.
  revert trace regs sigma regs' sigma' labels conditions.
  induction fuel as [|fuel IH]; intros trace regs sigma regs' sigma' labels conditions;
    [discriminate|].
  destruct trace as [|event rest|branches]; cbn [exec_trace].
  - intros [= <- <- <- <-]. constructor.
  - destruct (exec_event event rest regs sigma)
      as [[next [[[middle_regs middle_sigma] head] head_conditions]]|] eqn:Hstep;
      simpl; [|discriminate].
    destruct (exec_trace fuel next middle_regs middle_sigma)
      as [[[[final_regs final_sigma] tail] tail_conditions]|] eqn:Htail;
      simpl; [|discriminate].
    intros Heq. inversion Heq; subst.
    apply Forall_app. split.
    + eapply exec_event_success_conditions; exact Hstep.
    + eapply IH; exact Htail.
  - intros Hresult. destruct (first_result_member _ _ _ Hresult) as [branch [Hbranch Hexec]].
    eapply IH; exact Hexec.
Qed.
Print Assumptions exec_trace_success_conditions.

(** A future read pins a declaration before an event changes registers or memory. *)
Definition register_event_pin x event (regs : reg_map) : option (valu * base_val) :=
  match event with
  | ReadReg name al pattern _ =>
      match regs !! name, read_accessor al pattern with
      | Some actual, Some marker =>
          match read_accessor al actual with
          | Some actualValue =>
              match read_symbol x marker marker, read_symbol x marker actualValue with
              | Some (Val_Symbolic y), Some pinned =>
                  if bool_decide (x = y) && base_groundb pinned then Some (marker, pinned) else None
              | _, _ => None
              end
          | None => None
          end
      | _, _ => None
      end
  | _ => None
  end.
Lemma register_event_pin_sound x event regs marker pinned rest replacement :
  register_event_pin x event regs = Some (marker, pinned) ->
  RegisterReadPin x marker replacement pinned regs
    (subst_trace replacement x (event :t: rest)).
Proof.
  destruct event; simpl; try discriminate.
  destruct (regs !! name5) as [actual|] eqn:Hactual; [|discriminate].
  destruct (read_accessor accessor_list5 valu5) as [patternValue|] eqn:Hpattern; [|discriminate].
  destruct (read_accessor accessor_list5 actual) as [actualValue|] eqn:Haccessor; [|discriminate].
  destruct (read_symbol x patternValue patternValue) as [self|] eqn:Hself; [|discriminate].
  destruct self; try discriminate.
  destruct (read_symbol x patternValue actualValue) as [found|] eqn:Hfound; [|discriminate].
  destruct (bool_decide (x = vvar5) && base_groundb found) eqn:Hguard; [|discriminate].
  intros Heq. inversion Heq; subst marker found.
  apply andb_true_iff in Hguard as [Hsame Hground]. apply bool_decide_eq_true_1 in Hsame. subst vvar5.
  eapply RegisterReadPinHere with (actual := actual) (actualValue := actualValue)
    (patternValue := subst_val_valu replacement x patternValue).
  - exact Hactual.
  - exact Haccessor.
  - rewrite read_accessor_substitution Hpattern. reflexivity.
  - exact Hfound.
  - rewrite read_symbol_substitution_actual Hself. simpl. unfold eq_var_name. rewrite Z.eqb_refl. reflexivity.
Qed.
Print Assumptions register_event_pin_sound.
Fixpoint register_trace_pin fuel x regs trace : option (valu * base_val) :=
  match fuel, trace with
  | S fuel', tcons event rest =>
      if event_writesb event then None else
      match register_event_pin x event regs with
      | Some result => Some result
      | None => register_trace_pin fuel' x regs rest
      end
  | _, _ => None
  end.
Lemma register_trace_pin_sound fuel x regs trace marker pinned replacement :
  register_trace_pin fuel x regs trace = Some (marker, pinned) ->
  RegisterReadPin x marker replacement pinned regs (subst_trace replacement x trace).
Proof.
  revert trace. induction fuel as [|fuel IH]; intros [|event rest|branches]; simpl; try discriminate.
  destruct (event_writesb event) eqn:Hw; [discriminate|].
  destruct (register_event_pin x event regs) as [[foundMarker foundValue]|] eqn:Hpin.
  - intros [= <- <-]. eapply register_event_pin_sound; exact Hpin.
  - intros HpinTail. apply RegisterReadPinLater.
    + rewrite event_writesb_substitution. exact Hw.
    + apply IH. exact HpinTail.
Qed.
Print Assumptions register_trace_pin_sound.

Lemma register_event_pin_ground x event regs marker pinned :
  register_event_pin x event regs = Some (marker, pinned) -> base_ground pinned.
Proof.
  destruct event; simpl; try discriminate.
  destruct (regs !! name5) as [actual|] eqn:Hactual; [|discriminate].
  destruct (read_accessor accessor_list5 valu5) as [patternValue|] eqn:Hpattern; [|discriminate].
  destruct (read_accessor accessor_list5 actual) as [actualValue|] eqn:Haccessor; [|discriminate].
  destruct (read_symbol x patternValue patternValue) as [self|] eqn:Hself; [|discriminate].
  destruct self; try discriminate.
  destruct (read_symbol x patternValue actualValue) as [found|] eqn:Hfound; [|discriminate].
  destruct (bool_decide (x = vvar5) && base_groundb found) eqn:Hguard; [|discriminate].
  intros Heq. inversion Heq; subst marker found.
  apply andb_true_iff in Hguard as [Hsame Hground]. apply bool_decide_eq_true_1 in Hsame. subst vvar5.
  apply base_ground_reflect. exact Hground.
Qed.
Lemma register_trace_pin_ground fuel x regs trace marker pinned :
  register_trace_pin fuel x regs trace = Some (marker, pinned) -> base_ground pinned.
Proof.
  revert trace. induction fuel as [|fuel IH]; intros [|event rest|branches]; simpl; try discriminate.
  destruct (event_writesb event); [discriminate|].
  destruct (register_event_pin x event regs) as [[foundMarker foundValue]|] eqn:Hpin.
  - intros [= <- <-]. eapply register_event_pin_ground; exact Hpin.
  - apply IH.
Qed.
Lemma register_trace_pin_completed fuel x regs trace marker pinned replacement sigma labels theta' sigma' :
  register_trace_pin fuel x regs trace = Some (marker, pinned) ->
  base_ground replacement ->
  CompletedInstructionSegment (instruction_boundary (subst_trace replacement x trace) regs)
    sigma labels theta' sigma' -> replacement = pinned.
Proof.
  intros Hpin Hground Hrun. eapply register_read_pin_completed;
    [exact Hrun|eapply register_trace_pin_sound; exact Hpin|exact Hground].
Qed.
Print Assumptions register_event_pin_ground.
Print Assumptions register_trace_pin_ground.
Print Assumptions register_trace_pin_completed.

Definition RegisterEventPinSpec x event (regs : reg_map) marker pinned : Prop :=
  exists name al pattern ann actual actualValue,
    event = ReadReg name al pattern ann /\
    regs !! name = Some actual /\
    read_accessor al pattern = Some marker /\
    read_accessor al actual = Some actualValue /\
    read_symbol x marker marker = Some (Val_Symbolic x) /\
    read_symbol x marker actualValue = Some pinned /\
    base_ground pinned.
Lemma register_event_pin_reflect x event regs marker pinned :
  register_event_pin x event regs = Some (marker, pinned) <->
  RegisterEventPinSpec x event regs marker pinned.
Proof.
  split.
  -
    destruct event; simpl; try discriminate.
    destruct (regs !! name5) as [actual|] eqn:Hactual; [|discriminate].
    destruct (read_accessor accessor_list5 valu5) as [patternValue|] eqn:Hpattern; [|discriminate].
    destruct (read_accessor accessor_list5 actual) as [actualValue|] eqn:Haccessor; [|discriminate].
    destruct (read_symbol x patternValue patternValue) as [self|] eqn:Hself; [|discriminate].
    destruct self; try discriminate.
    destruct (read_symbol x patternValue actualValue) as [found|] eqn:Hfound; [|discriminate].
    destruct (bool_decide (x = vvar5) && base_groundb found) eqn:Hguard; [|discriminate].
    intros Heq. inversion Heq; subst marker found.
    apply andb_true_iff in Hguard as [Hsame Hground]. apply bool_decide_eq_true_1 in Hsame. subst vvar5.

    exists name5, accessor_list5, valu5, annot5, actual, actualValue.
    repeat split; try assumption; try reflexivity.
    apply base_ground_reflect. exact Hground.
  - intros (name & al & pattern & ann & actual & actualValue & Hevent & Hactual & Hpattern & Haccessor & Hself & Hfound & Hground).
    subst event. unfold register_event_pin.
    rewrite Hactual Hpattern Haccessor Hself Hfound.
    apply base_ground_reflect in Hground. rewrite bool_decide_true; [rewrite Hground; reflexivity|reflexivity].
Qed.
Print Assumptions register_event_pin_reflect.
Definition register_event_unpinned x event regs : Prop :=
  forall marker pinned, ~ RegisterEventPinSpec x event regs marker pinned.
Lemma register_event_unpinned_reflect x event regs :
  register_event_pin x event regs = None <-> register_event_unpinned x event regs.
Proof.
  unfold register_event_unpinned. split.
  - intros Hnone marker pinned Hpin. apply register_event_pin_reflect in Hpin. congruence.
  - destruct (register_event_pin x event regs) as [[marker pinned]|] eqn:Hpin; [|reflexivity].
    intros Hnone. exfalso. apply (Hnone marker pinned). apply register_event_pin_reflect. exact Hpin.
Qed.
Fixpoint RegisterTracePinSpec fuel x regs trace marker pinned : Prop :=
  match fuel, trace with
  | S fuel', tcons event rest =>
      event_writesb event = false /\
      (RegisterEventPinSpec x event regs marker pinned \/
       (register_event_unpinned x event regs /\ RegisterTracePinSpec fuel' x regs rest marker pinned))
  | _, _ => False
  end.
Lemma register_trace_pin_reflect fuel x regs trace marker pinned :
  register_trace_pin fuel x regs trace = Some (marker, pinned) <->
  RegisterTracePinSpec fuel x regs trace marker pinned.
Proof.
  revert trace. induction fuel as [|fuel IH]; intros [|event rest|branches]; simpl;
    try (split; [discriminate|contradiction]).
  destruct (event_writesb event) eqn:Hw; [split; [discriminate|intros [H _]; discriminate]|].
  destruct (register_event_pin x event regs) as [[foundMarker foundValue]|] eqn:Hpin.
  - split.
    + intros [= <- <-]. split; [reflexivity|left; apply register_event_pin_reflect; exact Hpin].
    + intros [_ [Hevent|[Hnone _]]].
      * apply register_event_pin_reflect in Hevent. rewrite Hpin in Hevent. exact Hevent.
      * apply register_event_unpinned_reflect in Hnone. congruence.
  - rewrite IH. split.
    + intros Htail. split; [reflexivity|right; split; [apply register_event_unpinned_reflect; exact Hpin|exact Htail]].
    + intros [_ [Hevent|[_ Htail]]]; [apply register_event_pin_reflect in Hevent; congruence|exact Htail].
Qed.
Definition register_pinningb fuel x regs trace : bool :=
  match register_trace_pin fuel x regs trace with Some _ => true | None => false end.
Lemma register_pinning_reflect fuel x regs trace :
  register_pinningb fuel x regs trace = true <->
  exists marker pinned, RegisterTracePinSpec fuel x regs trace marker pinned.
Proof.
  unfold register_pinningb. destruct (register_trace_pin fuel x regs trace) as [[marker pinned]|] eqn:Hpin.
  - split; [intros _; exists marker, pinned; apply register_trace_pin_reflect; exact Hpin|intros _; reflexivity].
  - split; [discriminate|intros (marker & pinned & Hspec); apply register_trace_pin_reflect in Hspec; congruence].
Qed.
Print Assumptions register_event_unpinned_reflect.
Print Assumptions register_trace_pin_reflect.
Print Assumptions register_pinning_reflect.

Lemma converted_address_equal (address : bvn) (pointer : bv 64) :
  bvn_to_bv 64 address = Some pointer -> RVal_Bits address = RVal_Bits pointer.
Proof.
  unfold bvn_to_bv. case_decide as Hwidth; [|discriminate].
  destruct address as [width payload]. simpl in Hwidth. subst width.
  intros [= <-]. reflexivity.
Qed.
Print Assumptions converted_address_equal.
Lemma rval_bits_injective (x y : bvn) : RVal_Bits x = RVal_Bits y -> x = y.
Proof. congruence. Qed.

Lemma seq_read_memory_equal predicted pinned (pointer : bv 64) kind len tag ann rest
    theta sigma labels theta' sigma' :
  seq_trace theta = ReadMem (RVal_Bits predicted) kind (RVal_Bits pointer) len tag ann :t: rest ->
  read_mem (seq_mem sigma) (bv_unsigned pointer) len = Some pinned ->
  seq_step theta sigma labels theta' sigma' [] ->
  seq_nb_state theta' = false ->
  predicted = pinned.
Proof.
  intros Htrace Hmemory Hstep Hnb. inversion Hstep; subst.
  match goal with H : trace_step _ _ _ _ |- _ => rewrite Htrace in H; inversion H; subst end.
  simpl in *.
  repeat match goal with
  | H : exists _, _ |- _ => destruct H as [? H]
  | H : _ /\ _ |- _ => destruct H as [? ?]
  end.
  assert (pointer = x) by (apply (rval_bv_injective 64 pointer x); exact H1).
  subst x.
  match goal with H : context [read_mem (seq_mem sigma) (bv_unsigned pointer) len] |- _ =>
    rewrite Hmemory in H; simpl in H end.
  repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  match goal with H : _ \/ _ |- _ => destruct H end.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  all: subst; simpl in Hnb; try discriminate.
  congruence.
Qed.
Print Assumptions seq_read_memory_equal.

Inductive MemoryReadPin (predicted pinned : bvn) (sigma : seq_global_state) : isla_trace -> Prop :=
| MemoryReadPinHere (pointer : bv 64) kind len tag ann rest :
    read_mem (seq_mem sigma) (bv_unsigned pointer) len = Some pinned ->
    MemoryReadPin predicted pinned sigma
      (ReadMem (RVal_Bits predicted) kind (RVal_Bits pointer) len tag ann :t: rest)
| MemoryReadPinLater e rest :
    event_writesb e = false ->
    MemoryReadPin predicted pinned sigma rest ->
    MemoryReadPin predicted pinned sigma (e :t: rest).
Lemma memory_read_pin_substitution predicted pinned sigma trace replacement y :
  MemoryReadPin predicted pinned sigma trace ->
  MemoryReadPin predicted pinned sigma (subst_trace replacement y trace).
Proof.
  intros Hpin. induction Hpin; simpl.
  - apply MemoryReadPinHere. assumption.
  - apply MemoryReadPinLater; [rewrite event_writesb_substitution; assumption|assumption].
Qed.
Lemma memory_read_pin_step predicted pinned sigma trace theta labels theta' sigma' :
  MemoryReadPin predicted pinned sigma trace ->
  seq_trace theta = trace ->
  seq_step theta sigma labels theta' sigma' [] ->
  seq_nb_state theta' = false ->
  predicted = pinned \/ MemoryReadPin predicted pinned sigma' (seq_trace theta').
Proof.
  intros Hpin Htrace Hstep Hnb.
  destruct Hpin as [pointer kind len tag ann rest Hmemory|e rest Hw Htail].
  - left. eapply seq_read_memory_equal; eassumption.
  - right.
    destruct (seq_step_keeps_trace theta sigma labels theta' sigma' Hstep Hnb)
      as [label [next [HtraceStep Hnext]]].
    destruct (seq_event_no_write e rest theta sigma labels theta' sigma' Htrace Hw Hstep)
      as [Hsigma' _].
    rewrite Htrace in HtraceStep.
    destruct (trace_cons_step_forms e rest (seq_regs theta) label next HtraceStep)
      as [[replacement [y Hform]]|Hform].
    + rewrite Hsigma' Hnext Hform. eapply memory_read_pin_substitution; eassumption.
    + rewrite Hsigma' Hnext Hform. exact Htail.
Qed.
Lemma memory_read_pin_prefix n theta sigma labels theta' sigma' predicted pinned :
  InstructionPrefix n theta sigma labels theta' sigma' ->
  MemoryReadPin predicted pinned sigma (seq_trace theta) ->
  seq_trace theta' = tnil ->
  predicted = pinned.
Proof.
  intros Hprefix. induction Hprefix; intros Hpin Hnil.
  - rewrite Hnil in Hpin. inversion Hpin.
  - destruct (memory_read_pin_step predicted pinned sigma (seq_trace theta)
      theta labels theta' sigma' Hpin eq_refl H0 H1) as [Heq|Hnext]; [exact Heq|].
    eapply IHHprefix; eassumption.
Qed.
Lemma memory_read_pin_completed theta sigma labels theta' sigma' predicted pinned :
  CompletedInstructionSegment theta sigma labels theta' sigma' ->
  MemoryReadPin predicted pinned sigma (seq_trace theta) ->
  predicted = pinned.
Proof.
  intros [n [boundary [memory [prefix [last [Hprefix [Hnil _]]]]]]] Hpin.
  eapply memory_read_pin_prefix; eassumption.
Qed.
Print Assumptions memory_read_pin_substitution.
Print Assumptions memory_read_pin_step.
Print Assumptions memory_read_pin_prefix.
Print Assumptions memory_read_pin_completed.


Definition memory_event_pin x event (sigma : seq_global_state) : option bvn :=
  match event with
  | ReadMem (RVal_Symbolic y) _ (RVal_Bits address) len _ _ =>
      if bool_decide (x = y) then
        pointer ← bvn_to_bv 64 address;
        read_mem (seq_mem sigma) (bv_unsigned pointer) len
      else None
  | _ => None
  end.
Lemma memory_event_pin_sound x event sigma pinned predicted rest :
  memory_event_pin x event sigma = Some pinned ->
  MemoryReadPin predicted pinned sigma
    (subst_trace (Val_Bits predicted) x (event :t: rest)).
Proof.
  destruct event; simpl; try discriminate.
  destruct valu5; try discriminate. destruct base_val5; try discriminate.
  destruct addr; try discriminate. destruct base_val5; try discriminate.
  destruct (bool_decide (x = vvar5)) eqn:Hsame; [|discriminate].
  apply bool_decide_eq_true in Hsame. subst vvar5.
  destruct (bvn_to_bv 64 bv5) as [pointer|] eqn:Hpointer; simpl; [|discriminate].
  intros Hmemory. unfold eq_var_name. rewrite Z.eqb_refl. simpl.
  pose proof (converted_address_equal bv5 pointer Hpointer) as Haddress.
  rewrite Haddress. apply MemoryReadPinHere. exact Hmemory.
Qed.
Print Assumptions memory_event_pin_sound.
Fixpoint memory_trace_pin fuel x sigma trace : option bvn :=
  match fuel, trace with
  | S fuel', tcons event rest =>
      if event_writesb event then None else
      match memory_event_pin x event sigma with
      | Some result => Some result
      | None => memory_trace_pin fuel' x sigma rest
      end
  | _, _ => None
  end.
Lemma memory_trace_pin_sound fuel x sigma trace pinned predicted :
  memory_trace_pin fuel x sigma trace = Some pinned ->
  MemoryReadPin predicted pinned sigma (subst_trace (Val_Bits predicted) x trace).
Proof.
  revert trace. induction fuel as [|fuel IH]; intros [|event rest|branches]; simpl; try discriminate.
  destruct (event_writesb event) eqn:Hw; [discriminate|].
  destruct (memory_event_pin x event sigma) as [found|] eqn:Hpin.
  - intros [= <-]. eapply memory_event_pin_sound; exact Hpin.
  - intros Htail. apply MemoryReadPinLater.
    + rewrite event_writesb_substitution. exact Hw.
    + apply IH. exact Htail.
Qed.
Lemma memory_trace_pin_completed fuel x sigma trace pinned predicted regs labels theta' sigma' :
  memory_trace_pin fuel x sigma trace = Some pinned ->
  CompletedInstructionSegment
    (instruction_boundary (subst_trace (Val_Bits predicted) x trace) regs)
    sigma labels theta' sigma' -> predicted = pinned.
Proof.
  intros Hpin Hrun. eapply memory_read_pin_completed;
    [exact Hrun|eapply memory_trace_pin_sound; exact Hpin].
Qed.
Print Assumptions memory_trace_pin_sound.
Print Assumptions memory_trace_pin_completed.

Definition base_option_sameb (left right : option base_val) : bool :=
  match left, right with
  | Some x, Some y => executor_base_eqb x y
  | None, None => true
  | _, _ => false
  end.
Lemma base_option_same_reflect left right : base_option_sameb left right = true <-> left = right.
Proof.
  destruct left; destruct right; simpl; try (split; [discriminate|congruence]); [|tauto].
  rewrite executor_base_eqb_reflect. split; congruence.
Qed.
Definition register_declaration_pinnedb x rest regs sigma : bool :=
  match register_trace_pin (isla_trace_length rest) x regs rest with
  | Some (_, pinned) => base_option_sameb
      (declaration_read (isla_trace_length rest) x rest regs sigma) (Some pinned)
  | None => false
  end.
Definition RegisterDeclarationPinned x rest regs sigma : Prop :=
  exists marker pinned,
    RegisterTracePinSpec (isla_trace_length rest) x regs rest marker pinned /\
    declaration_read (isla_trace_length rest) x rest regs sigma = Some pinned.
Lemma register_declaration_pinned_reflect x rest regs sigma :
  register_declaration_pinnedb x rest regs sigma = true <-> RegisterDeclarationPinned x rest regs sigma.
Proof.
  unfold register_declaration_pinnedb, RegisterDeclarationPinned.
  destruct (register_trace_pin (isla_trace_length rest) x regs rest) as [[marker pinned]|] eqn:Hpin.
  - rewrite base_option_same_reflect. split.
    + intros Hread. exists marker, pinned. split; [apply register_trace_pin_reflect; exact Hpin|exact Hread].
    + intros (marker' & pinned' & Hspec & Hread). apply register_trace_pin_reflect in Hspec.
      rewrite Hpin in Hspec. inversion Hspec; subst. exact Hread.
  - split; [discriminate|]. intros (marker & pinned & Hspec & Hread).
    apply register_trace_pin_reflect in Hspec. congruence.
Qed.
Definition memory_declaration_pinnedb declarationType x rest regs sigma : bool :=
  match declarationType with
  | Ty_BitVec _ =>
      match memory_trace_pin (isla_trace_length rest) x sigma rest with
      | Some pinned => base_option_sameb
          (declaration_read (isla_trace_length rest) x rest regs sigma) (Some (Val_Bits pinned))
      | None => false
      end
  | _ => false
  end.
Definition MemoryDeclarationPinned declarationType x rest regs sigma : Prop :=
  match declarationType with
  | Ty_BitVec _ => exists pinned,
      memory_trace_pin (isla_trace_length rest) x sigma rest = Some pinned /\
      declaration_read (isla_trace_length rest) x rest regs sigma = Some (Val_Bits pinned)
  | _ => False
  end.
Lemma memory_declaration_pinned_reflect declarationType x rest regs sigma :
  memory_declaration_pinnedb declarationType x rest regs sigma = true <->
  MemoryDeclarationPinned declarationType x rest regs sigma.
Proof.
  destruct declarationType; simpl; try (split; [discriminate|contradiction]).
  destruct (memory_trace_pin (isla_trace_length rest) x sigma rest) as [pinned|] eqn:Hpin.
  - rewrite base_option_same_reflect. split.
    + intros Hread. exists pinned. split; [reflexivity|exact Hread].
    + intros (pinned' & Hpin' & Hread). inversion Hpin'; subst. exact Hread.
  - split; [discriminate|]. intros (pinned & Hpin' & Hread). discriminate.
Qed.
Definition declaration_pinnedb x declarationType rest regs sigma : bool :=
  trace_unusedb x rest || register_declaration_pinnedb x rest regs sigma ||
    memory_declaration_pinnedb declarationType x rest regs sigma.
Definition DeclarationPinned x declarationType rest regs sigma : Prop :=
  trace_unused x rest \/ RegisterDeclarationPinned x rest regs sigma \/
    MemoryDeclarationPinned declarationType x rest regs sigma.
Lemma declaration_pinned_reflect x declarationType rest regs sigma :
  declaration_pinnedb x declarationType rest regs sigma = true <->
  DeclarationPinned x declarationType rest regs sigma.
Proof.
  unfold declaration_pinnedb, DeclarationPinned.
  rewrite !orb_true_iff trace_unused_reflect register_declaration_pinned_reflect memory_declaration_pinned_reflect.
  tauto.
Qed.
Print Assumptions base_option_same_reflect.
Print Assumptions register_declaration_pinned_reflect.
Print Assumptions memory_declaration_pinned_reflect.
Print Assumptions declaration_pinned_reflect.
Lemma declaration_pinned_forces_value x declarationType rest regs sigma replacement
    labels theta' sigma' :
  DeclarationPinned x declarationType rest regs sigma ->
  DeclarationValue declarationType replacement ->
  CompletedInstructionSegment (instruction_boundary (subst_trace replacement x rest) regs)
    sigma labels theta' sigma' ->
  trace_unusedb x rest = true \/
    declaration_read (isla_trace_length rest) x rest regs sigma = Some replacement.
Proof.
  intros [Hunused|[Hregister|Hmemory]] Hvalue Hrun.
  - left. apply trace_unused_reflect. exact Hunused.
  - right. destruct Hregister as (marker & pinned & Hpin & Hread).
    apply register_trace_pin_reflect in Hpin.
    assert (replacement = pinned) as ->.
    { eapply register_trace_pin_completed;
        [exact Hpin|eapply declaration_value_ground; exact Hvalue|exact Hrun]. }
    exact Hread.
  - right. destruct declarationType as [|width|name|first second]; simpl in Hmemory; try contradiction.
    destruct Hmemory as (pinned & Hpin & Hread).
    destruct Hvalue as [value ->].
    assert (bv_to_bvn value = pinned) as Heq.
    { eapply memory_trace_pin_completed; [exact Hpin|exact Hrun]. }
    rewrite <- Heq in Hread. exact Hread.
Qed.
Print Assumptions declaration_pinned_forces_value.
Lemma exec_declaration_agrees_with_completed x declarationType rest regs sigma replacement
    labels theta' sigma' next :
  DeclarationPinned x declarationType rest regs sigma ->
  DeclarationValue declarationType replacement ->
  CompletedInstructionSegment (instruction_boundary (subst_trace replacement x rest) regs)
    sigma labels theta' sigma' ->
  exec_declaration x declarationType rest regs sigma = Some next ->
  next = subst_trace replacement x rest.
Proof.
  intros Hpin Hvalue Hrun Hexec.
  destruct (declaration_pinned_forces_value x declarationType rest regs sigma replacement
      labels theta' sigma' Hpin Hvalue Hrun) as [Hunused|Hread].
  - rewrite (trace_unused_substitution x rest replacement Hunused).
    eapply exec_declaration_unused; [apply trace_unused_reflect; exact Hunused|exact Hexec].
  - rewrite (exec_declaration_matches_value x declarationType rest regs sigma replacement Hvalue Hread) in Hexec.
    inversion Hexec. reflexivity.
Qed.
Print Assumptions exec_declaration_agrees_with_completed.
Definition dead_assertionb event : bool :=
  match event with
  | Smt (Assert expression) _ =>
      match eval_exp expression with Some (Val_Bool false) => true | _ => false end
  | _ => false
  end.
Definition event_declaration_pinnedb event rest regs sigma : bool :=
  match event with
  | Smt (DeclareConst x declarationType) _ => declaration_pinnedb x declarationType rest regs sigma
  | _ => true
  end.
Definition EventDeclarationPinned event rest regs sigma : Prop :=
  match event with
  | Smt (DeclareConst x declarationType) _ => DeclarationPinned x declarationType rest regs sigma
  | _ => True
  end.
Lemma event_declaration_pinned_reflect event rest regs sigma :
  event_declaration_pinnedb event rest regs sigma = true <-> EventDeclarationPinned event rest regs sigma.
Proof.
  destruct event; try destruct smt5; simpl; try tauto.
  apply declaration_pinned_reflect.
Qed.
Fixpoint executor_pathb fuel trace regs sigma : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match trace with
      | tnil => true
      | event :t: rest =>
          if dead_assertionb event then true else
          memory_read_backedb event sigma && event_declaration_pinnedb event rest regs sigma &&
          match exec_event event rest regs sigma with
          | Some (next, (regs', sigma', _, _)) => executor_pathb fuel' next regs' sigma'
          | None => false
          end
      | tcases branches =>
          branches_exclusiveb branches && forallb (fun branch => executor_pathb fuel' branch regs sigma) branches
      end
  end.
Fixpoint ExecutorPath fuel trace regs sigma : Prop :=
  match fuel with
  | O => False
  | S fuel' =>
      match trace with
      | tnil => True
      | event :t: rest =>
          if dead_assertionb event then True else
          memory_read_backed event sigma /\ EventDeclarationPinned event rest regs sigma /\
          match exec_event event rest regs sigma with
          | Some (next, (regs', sigma', _, _)) => ExecutorPath fuel' next regs' sigma'
          | None => False
          end
      | tcases branches =>
          branches_exclusive branches /\ Forall (fun branch => ExecutorPath fuel' branch regs sigma) branches
      end
  end.
Lemma forallb_eq_true_reflect {A} (f : A -> bool) xs :
  forallb f xs = true <-> Forall (fun x => f x = true) xs.
Proof.
  induction xs as [|x xs IH]; simpl.
  - split; [intros _; constructor|intros _; reflexivity].
  -
  rewrite andb_true_iff Forall_cons IH. reflexivity.
Qed.
Lemma executor_path_reflect fuel trace regs sigma :
  executor_pathb fuel trace regs sigma = true <-> ExecutorPath fuel trace regs sigma.
Proof.
  revert trace regs sigma. induction fuel as [|fuel IH]; intros [|event rest|branches] regs sigma; simpl;
    try (split; [discriminate|contradiction]); try tauto.
  - destruct (dead_assertionb event); [tauto|].
    rewrite !andb_true_iff memory_read_backed_reflect event_declaration_pinned_reflect.
    destruct (exec_event event rest regs sigma) as [[next [[[regs' sigma'] labels] conditions]]|]; simpl.
    + rewrite IH. tauto.
    + split; [intros [_ H]; discriminate|tauto].
  - rewrite andb_true_iff branches_exclusive_reflect forallb_eq_true_reflect !Forall_forall.
    setoid_rewrite <- IH. reflexivity.
Qed.
Definition executor_deterministicb trace regs sigma : bool :=
  trace_exclusiveb trace && executor_pathb (S (isla_trace_length trace)) trace regs sigma.
Definition ExecutorDeterministic trace regs sigma : Prop :=
  trace_exclusive trace /\ ExecutorPath (S (isla_trace_length trace)) trace regs sigma.
Lemma executor_deterministic_reflect trace regs sigma :
  executor_deterministicb trace regs sigma = true <-> ExecutorDeterministic trace regs sigma.
Proof.
  unfold executor_deterministicb, ExecutorDeterministic.
  rewrite andb_true_iff trace_exclusive_reflect executor_path_reflect. reflexivity.
Qed.
Print Assumptions event_declaration_pinned_reflect.
Print Assumptions executor_path_reflect.
Print Assumptions executor_deterministic_reflect.

Definition BranchGuardPasses trace : Prop :=
  match trace with
  | Smt (Assert expression) _ :t: _ => eval_exp expression = Some (Val_Bool true)
  | _ => True
  end.
Lemma prefix_assert_eval_true n expression ann rest regs sigma labels boundary memory :
  InstructionPrefix n (instruction_boundary (Smt (Assert expression) ann :t: rest) regs)
    sigma labels boundary memory ->
  seq_trace boundary = tnil -> eval_exp expression = Some (Val_Bool true).
Proof.
  intros Hprefix Hnil. inversion Hprefix; subst.
  - discriminate Hnil.
  - eapply seq_assert_eval_true with (theta := instruction_boundary (Smt (Assert expression) ann :t: rest) regs); [reflexivity|eassumption|eassumption].
Qed.
Lemma prefix_branch_guard n trace regs sigma labels boundary memory :
  InstructionPrefix n (instruction_boundary trace regs) sigma labels boundary memory ->
  seq_trace boundary = tnil -> BranchGuardPasses trace.
Proof.
  destruct trace as [|event rest|branches]; simpl; try tauto.
  destruct event; simpl; try tauto.
  destruct smt5; simpl; try tauto. apply prefix_assert_eval_true.
Qed.
Lemma completed_branch_guard trace regs sigma labels theta' sigma' :
  CompletedInstructionSegment (instruction_boundary trace regs) sigma labels theta' sigma' ->
  BranchGuardPasses trace.
Proof.
  intros [n [boundary [memory [prefix [last [Hprefix [Hnil _]]]]]]].
  eapply prefix_branch_guard; eassumption.
Qed.
Lemma negated_pair_guards_not_both first second :
  negated_assertion_pair first second ->
  ~ (BranchGuardPasses first /\ BranchGuardPasses second).
Proof.
  unfold negated_assertion_pair, BranchGuardPasses.
  destruct first; destruct second; simpl; try tauto.
  all: repeat match goal with v : event |- _ => destruct v end; simpl; try tauto.
  all: repeat match goal with v : smt |- _ => destruct v end; simpl; try tauto.
  destruct exp5; simpl; try tauto. destruct unop5; simpl; try tauto.
  intros Heq [Hfirst Hsecond]. subst exp5.
  simpl in Hsecond. rewrite Hfirst in Hsecond. discriminate.
Qed.
Lemma complementary_guards_not_both first second :
  complementary_assertions first second ->
  ~ (BranchGuardPasses first /\ BranchGuardPasses second).
Proof.
  intros [Hpair|Hpair] [Hfirst Hsecond].
  - eapply negated_pair_guards_not_both; [exact Hpair|split; eassumption].
  - eapply negated_pair_guards_not_both; [exact Hpair|split; eassumption].
Qed.
Lemma branches_exclusive_guards_unique branches branch branch' :
  branches_exclusive branches -> branch ∈ branches -> branch' ∈ branches ->
  BranchGuardPasses branch -> BranchGuardPasses branch' -> branch = branch'.
Proof.
  destruct branches as [|first [|second [|third rest]]]; simpl;
    intros Hshape Hmember Hmember' Hrun Hrun'.
  - set_solver.
  - set_solver.
  - assert (Hfirst : branch = first \/ branch = second) by set_solver.
    assert (Hsecond : branch' = first \/ branch' = second) by set_solver.
    destruct Hfirst as [-> | ->]; destruct Hsecond as [-> | ->]; try reflexivity.
    + exfalso. eapply complementary_guards_not_both; [exact Hshape|split; eassumption].
    + exfalso. eapply complementary_guards_not_both; [exact Hshape|split; eassumption].
  - contradiction.
Qed.
Lemma exec_trace_branch_guard fuel trace regs sigma regs' sigma' labels conditions :
  exec_trace fuel trace regs sigma = Some (regs', sigma', labels, conditions) ->
  BranchGuardPasses trace.
Proof.
  intros Hexec. pose proof (exec_trace_success_conditions _ _ _ _ _ _ _ _ Hexec) as Hconditions.
  destruct (exec_trace_sound _ _ _ _ _ _ _ _ Hexec Hconditions) as [n Hprefix].
  eapply prefix_branch_guard; [exact Hprefix|reflexivity].
Qed.
Print Assumptions branches_exclusive_guards_unique.
Print Assumptions exec_trace_branch_guard.

Lemma completed_nil_step regs sigma labels theta' sigma' :
  CompletedInstructionSegment (instruction_boundary tnil regs) sigma labels theta' sigma' ->
  seq_step (instruction_boundary tnil regs) sigma labels theta' sigma' [].
Proof.
  intros [n [boundary [memory [prefix [last [Hprefix [Hnil [Hdone Hlabels]]]]]]]].
  inversion Hprefix; subst; [simpl in *; assumption|].
  simpl in H. contradiction.
Qed.
Lemma exec_finish_complete regs sigma labels theta' sigma' :
  seq_step (instruction_boundary tnil regs) sigma labels theta' sigma' [] ->
  exists conditions,
    exec_finish regs sigma = Some (theta', labels, conditions) /\
    ExecutorConditions conditions /\ seq_regs theta' = regs /\ sigma' = sigma.
Proof.
  intros Hstep. inversion Hstep; subst.
  match goal with H : trace_step _ _ _ _ |- _ => simpl in H; inversion H; subst end.
  simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  repeat match goal with H : exists _, _ |- _ => destruct H as [? H] end.
  repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  destruct (seq_instrs sigma !! x) as [next|] eqn:Hnext;
    repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end; subst.
  all: unfold exec_finish; rewrite H2; rewrite Z_to_bv_bv_unsigned; rewrite Hnext; simpl.
  all: eexists; split; [reflexivity|]; split; [constructor; [reflexivity|constructor]|]; split; reflexivity.
Qed.
Print Assumptions completed_nil_step.
Print Assumptions exec_finish_complete.

Lemma exec_nondeclaration_completed_follow event rest regs sigma labels theta' sigma'
    next regs1 sigma1 first conditions :
  event_declares event = false ->
  exec_event event rest regs sigma = Some (next, (regs1, sigma1, first, conditions)) ->
  CompletedInstructionSegment (instruction_boundary (event :t: rest) regs)
    sigma labels theta' sigma' ->
  exists tail,
    CompletedInstructionSegment (instruction_boundary next regs1) sigma1 tail theta' sigma' /\
    labels = first ++ tail.
Proof.
  intros Hdecl Hexec Hrun.
  destruct (completed_cons_invert event rest (instruction_boundary (event :t: rest) regs)
      sigma labels theta' sigma' eq_refl Hrun)
    as (formalFirst & formalTheta & formalSigma & tail & Hstep & Hnb & Htail & Hlabels).
  pose proof (exec_event_success_conditions _ _ _ _ _ _ _ _ _ Hexec) as Hconditions.
  pose proof (exec_event_sound _ _ _ _ _ _ _ _ _ Hexec Hconditions) as Hcomputed.
  destruct (seq_nondeclaration_unique event rest (instruction_boundary (event :t: rest) regs)
      sigma formalFirst formalTheta formalSigma first (instruction_boundary next regs1) sigma1
      eq_refl Hdecl Hstep Hnb Hcomputed eq_refl) as (Hfirst & Htheta & Hsigma).
  subst formalFirst formalTheta formalSigma. exists tail. auto.
Qed.
Lemma exec_event_completed_follow event rest regs sigma labels theta' sigma'
    next regs1 sigma1 first conditions :
  EventDeclarationPinned event rest regs sigma ->
  exec_event event rest regs sigma = Some (next, (regs1, sigma1, first, conditions)) ->
  CompletedInstructionSegment (instruction_boundary (event :t: rest) regs)
    sigma labels theta' sigma' ->
  exists tail,
    CompletedInstructionSegment (instruction_boundary next regs1) sigma1 tail theta' sigma' /\
    labels = first ++ tail.
Proof.
  intros Hpin Hexec Hrun.
  destruct (event_declares event) eqn:Hdecl.
  2: { eapply exec_nondeclaration_completed_follow; eassumption. }
  destruct event; simpl in Hdecl; try discriminate.
  destruct smt5; simpl in Hdecl; try discriminate.
  cbn [EventDeclarationPinned] in Hpin. cbn [exec_event] in Hexec.
  destruct (exec_declaration vvar5 ty5 rest regs sigma) as [computed|] eqn:Hdeclaration; simpl; [|discriminate].
  inversion Hexec; subst next regs1 sigma1 first conditions; clear Hexec.
  destruct (completed_declaration_invert _ _ _ _ _ _ _ _ _ Hrun) as (replacement & Hvalue & Htail).
  pose proof (exec_declaration_agrees_with_completed _ _ _ _ _ _ _ _ _ _
      Hpin Hvalue Htail Hdeclaration) as Heq. subst computed.
  exists labels. split; [exact Htail|reflexivity].
Qed.
Lemma first_result_complete_unique {A B} (f : A -> option B) xs x result :
  x ∈ xs -> f x = Some result ->
  (forall y result', y ∈ xs -> f y = Some result' -> result' = result) ->
  first_result f xs = Some result.
Proof.
  induction xs as [|y ys IH]; simpl; [set_solver|].
  intros Hx Hfx Hunique. destruct (f y) as [r|] eqn:Hy.
  - f_equal. eapply (Hunique y r); [set_solver|exact Hy].
  - eapply IH; [|exact Hfx|].
    + assert (x = y \/ x ∈ ys) by set_solver. destruct H; [subst; congruence|assumption].
    + intros z value Hz Hvalue. eapply (Hunique z value); [set_solver|exact Hvalue].
Qed.
Lemma exec_trace_completed fuel trace regs sigma labels theta' sigma' :
  ExecutorPath fuel trace regs sigma ->
  CompletedInstructionSegment (instruction_boundary trace regs) sigma labels theta' sigma' ->
  exists finalRegs finalSigma body bodyConditions last finishConditions,
    exec_trace fuel trace regs sigma = Some (finalRegs, finalSigma, body, bodyConditions) /\
    exec_finish finalRegs finalSigma = Some (theta', last, finishConditions) /\
    ExecutorConditions bodyConditions /\ ExecutorConditions finishConditions /\
    seq_regs theta' = finalRegs /\ sigma' = finalSigma /\ labels = body ++ last.
Proof.
  revert trace regs sigma labels theta' sigma'. induction fuel as [|fuel IH];
    intros trace regs sigma labels theta' sigma' Hpath Hrun; [contradiction|].
  destruct trace as [|event rest|branches].
  - apply completed_nil_step in Hrun.
    destruct (exec_finish_complete _ _ _ _ _ Hrun) as (conditions & Hfinish & Hconditions & Hregs & Hsigma).
    exists regs, sigma, [], [], labels, conditions. simpl. repeat split; try assumption. constructor.
  - cbn [ExecutorPath] in Hpath.
    destruct (dead_assertionb event) eqn:Hdead.
    + unfold dead_assertionb in Hdead. destruct event; try discriminate.
      destruct smt5; try discriminate.
      pose proof (completed_assert_eval_true _ _ _ _ _ _ _ _ Hrun) as Heval.
      rewrite Heval in Hdead. discriminate.
    + destruct Hpath as (Hbacked & Hpin & Hpath).
      destruct (exec_event event rest regs sigma) as [[next [[[regs1 sigma1] first] conditions]]|] eqn:Hexec;
        [|contradiction].
      destruct (exec_event_completed_follow _ _ _ _ _ _ _ _ _ _ _ _
          Hpin Hexec Hrun) as (tail & Htail & Hlabels).
      destruct (IH _ _ _ _ _ _ Hpath Htail)
        as (finalRegs & finalSigma & body & bodyConditions & last & finishConditions &
            Htrace & Hfinish & Hbody & HfinishConditions & Hregs & Hsigma & HtailLabels).
      exists finalRegs, finalSigma, (first ++ body), (conditions ++ bodyConditions), last, finishConditions.
      split.
      * cbn [exec_trace]. rewrite Hexec. simpl. rewrite Htrace. reflexivity.
      * split; [exact Hfinish|]. split.
        -- unfold ExecutorConditions. apply Forall_app. split; [eapply exec_event_success_conditions; exact Hexec|exact Hbody].
        -- repeat split; try assumption. rewrite Hlabels HtailLabels app_assoc. reflexivity.
  - cbn [ExecutorPath] in Hpath. destruct Hpath as [Hshape Hbranches].
    destruct (completed_cases_invert _ _ _ _ _ _ Hrun) as (branch & Hmember & Hbranch).
    rewrite Forall_forall in Hbranches.
    destruct (IH _ _ _ _ _ _ (Hbranches branch Hmember) Hbranch)
      as (finalRegs & finalSigma & body & bodyConditions & last & finishConditions &
          Htrace & Hfinish & Hbody & HfinishConditions & Hregs & Hsigma & Hlabels).
    exists finalRegs, finalSigma, body, bodyConditions, last, finishConditions.
    split; [|repeat split; assumption]. cbn [exec_trace].
    eapply first_result_complete_unique; [exact Hmember|exact Htrace|].
    intros alternative result Hmember' Hexec.
    assert (alternative = branch) as ->.
    { eapply branches_exclusive_guards_unique; [exact Hshape|exact Hmember'|exact Hmember| |].
      - destruct result as [[[r s] ls] cs]. eapply exec_trace_branch_guard; exact Hexec.
      - eapply completed_branch_guard; exact Hbranch. }
    congruence.
Qed.
Print Assumptions exec_trace_completed.
Theorem exec_instr_deterministic trace regs sigma labels theta' sigma' :
  executor_deterministicb trace regs sigma = true ->
  CompletedInstructionSegment (instruction_boundary trace regs) sigma labels theta' sigma' ->
  exists conditions,
    exec_instr trace regs sigma = Some (seq_regs theta', sigma', labels, conditions) /\
    ExecutorConditions conditions.
Proof.
  intros Hdet Hrun. apply executor_deterministic_reflect in Hdet. destruct Hdet as [_ Hpath].
  destruct (exec_trace_completed _ _ _ _ _ _ _ Hpath Hrun)
    as (finalRegs & finalSigma & body & bodyConditions & last & finishConditions &
        Htrace & Hfinish & Hbody & HfinishConditions & Hregs & Hsigma & Hlabels).
  exists (bodyConditions ++ finishConditions). split.
  - unfold exec_instr. rewrite Htrace. simpl. rewrite Hfinish. simpl.
    rewrite Hregs Hsigma Hlabels. reflexivity.
  - unfold ExecutorConditions in *. apply Forall_app. auto.
Qed.
Print Assumptions exec_instr_deterministic.
