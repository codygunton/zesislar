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

