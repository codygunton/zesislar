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
