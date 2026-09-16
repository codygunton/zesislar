Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Executor.

Definition executorNextBoundary (regs : reg_map) (sigma : seq_global_state) :
    seq_local_state :=
  match regs !! "PC" with
  | Some (RVal_Bits address) =>
      match sigma.(seq_instrs) !! Z_to_bv 64 (bvn_unsigned address) with
      | Some next => instruction_boundary next regs
      | None => instruction_boundary tnil regs <| seq_nb_state := true |>
      end
  | _ => instruction_boundary tnil regs
  end.

Lemma exec_finish_boundary regs sigma theta labels conditions :
  exec_finish regs sigma = Some (theta, labels, conditions) ->
  theta = executorNextBoundary regs sigma.
Proof.
  unfold exec_finish, executorNextBoundary.
  destruct (regs !! "PC") as [value|]; [|discriminate].
  destruct value; try discriminate. destruct base_val5; try discriminate.
  destruct (seq_instrs sigma !! Z_to_bv 64 (bvn_unsigned bv5));
    intros Heq; inversion Heq; reflexivity.
Qed.

Lemma exec_instr_boundary_sound trace regs sigma regs' sigma' labels conditions :
  exec_instr trace regs sigma = Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions ->
  CompletedInstructionSegment (instruction_boundary trace regs) sigma labels
    (executorNextBoundary regs' sigma') sigma'.
Proof.
  unfold exec_instr.
  destruct (exec_trace (S (isla_trace_length trace)) trace regs sigma)
    as [[[[finalRegs finalSigma] prefix] prefixConditions]|] eqn:Htrace;
    simpl; [|discriminate].
  destruct (exec_finish finalRegs finalSigma)
    as [[[theta last] lastConditions]|] eqn:Hfinish;
    simpl; [|discriminate].
  intros Heq Hconditions. inversion Heq; subst; clear Heq.
  apply Forall_app in Hconditions.
  destruct Hconditions as [HprefixConditions HlastConditions].
  destruct (exec_trace_sound _ _ _ _ _ _ _ _ Htrace HprefixConditions)
    as [count Hprefix].
  destruct (exec_finish_sound _ _ _ _ _ Hfinish HlastConditions)
    as [_ Hstep].
  apply exec_finish_boundary in Hfinish. subst theta.
  exists count, (instruction_boundary tnil regs'), sigma', prefix, last.
  repeat split; auto.
Qed.

Lemma executor_next_boundary_continue regs sigma :
  seq_nb_state (executorNextBoundary regs sigma) = false ->
  executorNextBoundary regs sigma =
    instruction_boundary (seq_trace (executorNextBoundary regs sigma)) regs.
Proof.
  unfold executorNextBoundary.
  destruct (regs !! "PC") as [value|]; [|reflexivity].
  destruct value; try reflexivity. destruct base_val5; try reflexivity.
  destruct (seq_instrs sigma !! Z_to_bv 64 (bvn_unsigned bv5));
    simpl; [reflexivity|discriminate].
Qed.

Record ProgramExecutorResult : Type := {
  programResultLocal : seq_local_state;
  programResultGlobal : seq_global_state;
  programResultLabels : list seq_label;
  programResultConditions : list Prop
}.

Fixpoint exec_program (fuel : nat) (trace : isla_trace) (regs : reg_map)
    (sigma : seq_global_state) : option ProgramExecutorResult :=
  match fuel with
  | O => None
  | S fuel' =>
      match exec_instr trace regs sigma with
      | None => None
      | Some (regs', sigma', labels, conditions) =>
          let next := executorNextBoundary regs' sigma' in
          if next.(seq_nb_state) then
            Some {| programResultLocal := next;
                    programResultGlobal := sigma';
                    programResultLabels := labels;
                    programResultConditions := conditions |}
          else
            match exec_program fuel' next.(seq_trace) regs' sigma' with
            | None => None
            | Some result =>
                Some {| programResultLocal := result.(programResultLocal);
                        programResultGlobal := result.(programResultGlobal);
                        programResultLabels := labels ++ result.(programResultLabels);
                        programResultConditions :=
                          conditions ++ result.(programResultConditions) |}
            end
      end
  end.

Theorem exec_program_sound fuel trace regs sigma result :
  exec_program fuel trace regs sigma = Some result ->
  ExecutorConditions result.(programResultConditions) ->
  exists instructions,
    CompletedInstructionRun instructions (instruction_boundary trace regs) sigma
      result.(programResultLabels) result.(programResultLocal)
      result.(programResultGlobal) /\
    result.(programResultLocal).(seq_nb_state) = true.
Proof.
  revert trace regs sigma result.
  induction fuel as [|fuel IH]; intros trace regs sigma result Hexec Hconditions;
    [discriminate|].
  cbn [exec_program] in Hexec.
  destruct (exec_instr trace regs sigma)
    as [[[[regs' sigma'] labels] conditions]|] eqn:Hinstruction;
    [|discriminate].
  set (next := executorNextBoundary regs' sigma') in *.
  destruct (seq_nb_state next) eqn:Hterminal.
  - inversion Hexec; subst; clear Hexec.
    exists 1%nat. split; [|exact Hterminal].
    replace labels with (labels ++ []) by apply app_nil_r.
    econstructor.
    + eapply exec_instr_boundary_sound; eassumption.
    + constructor.
  - destruct (exec_program fuel (seq_trace next) regs' sigma')
      as [rest|] eqn:Hrest; [|discriminate].
    inversion Hexec; subst; clear Hexec.
    apply Forall_app in Hconditions.
    destruct Hconditions as [HinstructionConditions HrestConditions].
    destruct (IH _ _ _ _ Hrest HrestConditions)
      as [instructions [Hrun Hfinish]].
    exists (S instructions). split; [|exact Hfinish].
    assert (Hnext : next = instruction_boundary (seq_trace next) regs').
    { subst next. apply executor_next_boundary_continue. exact Hterminal. }
    rewrite <- Hnext in Hrun.
    cbn.
    econstructor.
    + eapply exec_instr_boundary_sound; eassumption.
    + exact Hrun.
Qed.

Print Assumptions exec_finish_boundary.
Print Assumptions exec_instr_boundary_sound.
Print Assumptions executor_next_boundary_continue.
Print Assumptions exec_program_sound.
