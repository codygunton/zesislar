Require Import ZesuSsz.Automation.All.
From Coq Require Import Lia.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Executor.
Require Import ZesuSsz.Proofs.Termination.ControlExecutor.

Lemma executor_next_boundary_regs regs sigma :
  seq_regs (executorNextBoundary regs sigma) = regs.
Proof.
  unfold executorNextBoundary.
  destruct (regs !! "PC") as [value|]; [|reflexivity].
  destruct value; try reflexivity. destruct base_val5; try reflexivity.
  destruct (seq_instrs sigma !! Z_to_bv 64 (bvn_unsigned bv5)); reflexivity.
Qed.

(** The halt test selects a contract boundary before the executor runs it. *)
Fixpoint exec_program_until
    (halt : reg_map -> seq_global_state -> bool)
    (fuel : nat) (trace : isla_trace) (regs : reg_map)
    (sigma : seq_global_state) : option ProgramExecutorResult :=
  if halt regs sigma then
    Some {| programResultLocal := instruction_boundary trace regs;
            programResultGlobal := sigma;
            programResultLabels := [];
            programResultConditions := [] |}
  else
    match fuel with
    | O => None
    | S fuel' =>
        match exec_instr trace regs sigma with
        | None => None
        | Some (regs', sigma', labels, conditions) =>
            let next := executorNextBoundary regs' sigma' in
            if halt regs' sigma' then
              Some {| programResultLocal := next;
                      programResultGlobal := sigma';
                      programResultLabels := labels;
                      programResultConditions := conditions |}
            else if next.(seq_nb_state) then None
            else
              match exec_program_until halt fuel' next.(seq_trace) regs' sigma' with
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

Theorem exec_program_until_sound halt fuel trace regs sigma result :
  exec_program_until halt fuel trace regs sigma = Some result ->
  ExecutorConditions result.(programResultConditions) ->
  exists instructions,
    (instructions <= fuel)%nat /\
    CompletedInstructionRun instructions (instruction_boundary trace regs) sigma
      result.(programResultLabels) result.(programResultLocal)
      result.(programResultGlobal) /\
    halt (seq_regs result.(programResultLocal)) result.(programResultGlobal) = true.
Proof.
  revert trace regs sigma result.
  induction fuel as [|fuel IH]; intros trace regs sigma result Hexec Hconditions.
  - cbn [exec_program_until] in Hexec.
    destruct (halt regs sigma) eqn:Hhalt; [|discriminate].
    inversion Hexec; subst; clear Hexec.
    exists 0%nat. split; [lia|]. split; [constructor|exact Hhalt].
  - cbn [exec_program_until] in Hexec.
    destruct (halt regs sigma) eqn:Hhalt.
    + inversion Hexec; subst; clear Hexec.
      exists 0%nat. split; [lia|]. split; [constructor|exact Hhalt].
    + destruct (exec_instr trace regs sigma)
        as [[[[regs' sigma'] labels] conditions]|] eqn:Hinstruction;
        [|discriminate].
      set (next := executorNextBoundary regs' sigma') in *.
      destruct (halt regs' sigma') eqn:HnextHalt.
      * inversion Hexec; subst; clear Hexec.
        exists 1%nat. split; [lia|]. split.
        -- replace labels with (labels ++ []) by apply app_nil_r.
           econstructor.
           ++ eapply exec_instr_boundary_sound; eassumption.
           ++ constructor.
        -- simpl. subst next. rewrite executor_next_boundary_regs. exact HnextHalt.
      * destruct (seq_nb_state next) eqn:Hterminal; [discriminate|].
        destruct (exec_program_until halt fuel (seq_trace next) regs' sigma')
          as [rest|] eqn:Hrest; [|discriminate].
        inversion Hexec; subst; clear Hexec.
        apply Forall_app in Hconditions.
        destruct Hconditions as [HinstructionConditions HrestConditions].
        destruct (IH _ _ _ _ Hrest HrestConditions)
          as [instructions [Hbound [Hrun Hfinish]]].
        exists (S instructions). split; [lia|]. split; [|exact Hfinish].
        assert (Hnext : next = instruction_boundary (seq_trace next) regs').
        { subst next. apply executor_next_boundary_continue. exact Hterminal. }
        rewrite <- Hnext in Hrun.
        cbn. econstructor.
        -- eapply exec_instr_boundary_sound; eassumption.
        -- exact Hrun.
Qed.

Print Assumptions executor_next_boundary_regs.
Print Assumptions exec_program_until_sound.
