(** Project-wide Lithium hook redefinitions belong in this module. *)

From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.
Require Export ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.NatBounds.
Require Import ZesuMachineMap.Machine.

(** Give Lithium its separating-conjunction goal form. *)
Ltac zesu_prepare_uninit_goal :=
  lazymatch goal with
  | |- envs_entails _ (?address ↦ₘ? ?count)%I =>
      iEval (rewrite -(right_id True%I _ (address ↦ₘ? count)%I))
  end.

(** Normalize the reviewed map before bitvector arithmetic. *)
Ltac zesu_normalize_machine_map :=
  cbv [mapRamBase mapRamSize mapIoContextAddress mapTextBase
    machineRamEnd machineOutputAddress machineOutputSizeAddress
    machineExitAddress machinePc defaultMap] in *.

(** Name a machine bound after normalizing its reviewed map fields. *)
Ltac zesu_name_machine_bound expected name :=
  let normalizedExpected := eval cbv [mapRamBase mapRamSize
    mapIoContextAddress mapTextBase machineRamEnd machineOutputAddress
    machineOutputSizeAddress machineExitAddress machinePc defaultMap Z.add Z.sub]
    in expected in
  match goal with
  | H : ?actual |- _ =>
      let normalizedActual := eval cbv [mapRamBase mapRamSize
        mapIoContextAddress mapTextBase machineRamEnd machineOutputAddress
        machineOutputSizeAddress machineExitAddress machinePc defaultMap Z.add Z.sub]
        in actual in
      constr_eq normalizedActual normalizedExpected;
      rename H into name
  end.

Ltac zesu_solve_machine_bounds :=
  solve [zesu_normalize_binary_nat_hypotheses;
    zesu_normalize_binary_nat_goal; zesu_normalize_machine_map; bv_solve].
Ltac zesu_solve_machine_linear :=
  first [solve [repeat match goal with
           | Hnat : (_ <= _)%nat |- _ => clear Hnat
           | Hnat : (_ < _)%nat |- _ => clear Hnat
           end; zesu_normalize_machine_map; lia] |
    solve [zesu_normalize_binary_nat_hypotheses;
      zesu_normalize_binary_nat_goal; zesu_normalize_machine_map; lia]].
Tactic Notation "lia" := zesu_solve_machine_linear.

Tactic Notation "bv_solve" := zesu_solve_machine_bounds.

Ltac zesu_normalize_symbolic_mem_address :=
  repeat match goal with
  | Hlocal := _ |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      lazymatch address with context[Hlocal] => unfold Hlocal in *; clear Hlocal end
  end;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo (bv_unsigned ?pointer)) _) =>
    let expanded := eval cbv beta zeta in pointer in
    lazymatch expanded with
    | bv_add ?base ?offset =>
      lazymatch base with
      | bv_add ?root ?displacement => is_var root
      | bv_sub ?root ?displacement => is_var root
      end;
      let integer := eval vm_compute in (bv_unsigned offset) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac end;
      let Heq := fresh "HmemoryAddress" in
      assert (Heq : bv_unsigned pointer = (bv_unsigned base + integer)%Z) by
        (repeat match goal with
         | Hnat : (_ <= _)%nat |- _ => clear Hnat
         | Hnat : (_ < _)%nat |- _ => clear Hnat
         end; bv_solve);
      rewrite Heq; clear Heq
    end
  end.

Ltac zesu_has_known_word_address expected spatial :=
  lazymatch spatial with
  | Esnoc ?rest _ ((?actual ↦ₘ{?q} ?word)%I) =>
      first [constr_eq actual expected | zesu_has_known_word_address expected rest]
  | Esnoc ?rest _ _ => zesu_has_known_word_address expected rest
  end.
Ltac zesu_normalize_known_word_address :=
  repeat match goal with
  | Hlocal := _ |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      lazymatch address with context[Hlocal] => unfold Hlocal in *; clear Hlocal end
  end;
  lazymatch goal with
  | |- envs_entails ?context
      (find_in_context (FindMemMapsTo (bv_unsigned ?pointer)) _) =>
      let expanded := eval cbv beta zeta in pointer in
      lazymatch expanded with bv_add ?base ?offset =>
      is_var base;
      let integer := eval vm_compute in (bv_unsigned offset) in
      let expected := constr:((bv_unsigned base + integer)%Z) in
      let spatial := eval cbn [env_spatial] in (env_spatial context) in
      zesu_has_known_word_address expected spatial;
      let Heq := fresh "HknownWordAddress" in
      assert (Heq : bv_unsigned pointer = expected) by bv_solve;
      rewrite Heq; clear Heq
      end
  end.
Ltac zesu_normalize_find_mem_address :=
  first [zesu_normalize_symbolic_mem_address | zesu_normalize_known_word_address].


Ltac zesu_unfold_bv_bindings :=
  repeat match goal with
  | Hlocal := _ : bv _ |- _ => unfold Hlocal in *; clear Hlocal
  end.

Ltac zesu_normalize_memory_cell H expected :=
  let selected := iTypeOf (INamed H) in
  lazymatch selected with
  | Some (_, (?actual ↦ₘ{?q} ?value)%I) =>
      let Heq := fresh "HcellAddress" in
      assert (Heq : actual = expected) by bv_solve;
      iEval (rewrite Heq) in H; clear Heq
  end.

Ltac zesu_solve_pending_sidecond :=
  lazymatch goal with
  | |- envs_entails _ _ => fail
  | _ => prepare_sidecond; first [assumption | bv_solve | lia]
  end.

Ltac zesu_normalize_output_address :=
  lazymatch goal with
  | |- envs_entails _
      (WPasm (WriteMem _ _ (RVal_Bits (bv_to_bvn ?address)) _ _ _ _ :t: _)) =>
      first [replace address with (BV 64 (machineOutputAddress defaultMap))
               by (vm_compute; bv_solve)
            |replace address with (BV 64 (machineOutputSizeAddress defaultMap))
               by (vm_compute; bv_solve)
            |idtac]
  | _ => idtac
  end.

Ltac zesu_liAReadMem :=
  lazymatch goal with
  | |- envs_entails ?Delta
      (WPasm (ReadMem _ _ _ _ _ _ :t: _)) =>
      notypeclasses refine
        (tac_fast_apply (li_wp_read_mem_zesu _ _ _ _ _ _ _ _) _)
  end.

Ltac zesu_liAWriteMem :=
  lazymatch goal with
  | |- envs_entails ?Delta
      (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) =>
      unshelve (notypeclasses refine
        (tac_fast_apply (li_wp_write_mem_zesu _ _ _ _ _ _ _ _ _) _))
  end.

Ltac zesu_liAWriteMemFocused :=
  zesu_normalize_output_address;
  lazymatch goal with
  | |- envs_entails ?Delta
      (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) =>
      notypeclasses refine
        (tac_fast_apply (li_wp_write_mem_zesu _ _ _ _ _ _ _ _ _) _)
  end.

Ltac zesu_liASnapshotWriteMem :=
  lazymatch goal with
  | |- envs_entails ?Delta
      (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) =>
      unshelve (notypeclasses refine
        (tac_fast_apply
          (li_wp_write_mmio_snapshot_zesu _ _ _ _ _ _ _ _ _ _) _))
  end.

Ltac zesu_liASnapshotWriteMemFocused :=
  zesu_normalize_output_address;
  lazymatch goal with
  | |- envs_entails ?Delta
      (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) =>
      notypeclasses refine
        (tac_fast_apply
          (li_wp_write_mmio_snapshot_zesu _ _ _ _ _ _ _ _ _ _) _)
  end.

Ltac zesu_liASnapshotWriteMemAt claimAddress :=
  zesu_normalize_output_address;
  lazymatch goal with
  | |- envs_entails ?Delta
      (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) =>
      notypeclasses refine
        (tac_fast_apply
          (li_wp_write_mmio_snapshot_zesu _ _ _ _ _ _ _ _ _ claimAddress) _)
  end.

Ltac zesu_liAAsmNoWrite :=
  lazymatch goal with
  | |- envs_entails _ (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) => fail 1
  | _ => liAAsm
  end.

Ltac zesu_liAAsmBeforeObservable :=
  lazymatch goal with
  | |- envs_entails _ (WPasm (WriteMem _ _ _ _ _ _ _ :t: _)) => fail 1
  | |- envs_entails _ (WPasm tnil) => fail 1
  | _ => liAAsm
  end.

Ltac zesu_liAStepNoWrite :=
 liEnsureInvariant;
 try liAIntroduceLetInGoal;
 first [
    zesu_normalize_find_mem_address
  | zesu_liAReadMem
  | zesu_liAAsmNoWrite
  | liAExp
  | liAOther
  | liUnfoldEarly
  | liStep
  | liLetBindHint
  | liUnfoldLate
 ]; liSimpl.

Ltac zesu_liAStepBeforeObservable :=
 liEnsureInvariant;
 try liAIntroduceLetInGoal;
 first [
    zesu_normalize_find_mem_address
  | zesu_liAReadMem
  | zesu_liAAsmBeforeObservable
  | liAExp
  | liAOther
  | liUnfoldEarly
  | liStep
  | liLetBindHint
  | liUnfoldLate
 ]; liSimpl.

Ltac zesu_liAStepSnapshotWrite :=
 liEnsureInvariant;
 try liAIntroduceLetInGoal;
 zesu_liASnapshotWriteMemFocused.

Ltac zesu_liAStepSnapshotWriteAt claimAddress :=
 liEnsureInvariant;
 try liAIntroduceLetInGoal;
 zesu_liASnapshotWriteMemAt claimAddress.

Ltac zesu_liAStepGenericWrite :=
 liEnsureInvariant;
 try liAIntroduceLetInGoal;
 zesu_liAWriteMemFocused.

Ltac zesu_liAStep :=
 liEnsureInvariant;
 try progress (unfold TRACE_LET);
 try liAIntroduceLetInGoal;
 first [
    zesu_normalize_find_mem_address
  | zesu_liAWriteMem
  | zesu_liAReadMem
  | liAAsm
  | liAExp
  | liAOther
  | liUnfoldEarly
  | liStep
  | liLetBindHint
  | liUnfoldLate
 ]; liSimpl.

Ltac liAStep ::= zesu_liAStep.
