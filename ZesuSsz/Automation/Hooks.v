(** Project-wide Lithium hook redefinitions belong in this module. *)

From iris.proofmode Require Import environments intro_patterns ltac_tactics reduction.
Require Import ZesuSsz.Automation.ReturnBundle.
Require Import ZesuSsz.Automation.ArraySlices.
Require Export ZesuSsz.Automation.ByteScratchReuse.
Require Export ZesuSsz.Automation.WordArrayIndex.
Require Export ZesuSsz.Automation.OwnedPayloadPackages.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require Export ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.NatBounds.
Require Import ZesuSsz.Automation.BoundedArithmetic.
Require Import ZesuSsz.Automation.TraceTailLemmas.
Require Import ZesuSsz.Automation.InstrPre.
Require Import ZesuSsz.Automation.SpecPrefix.
Require Import ZesuSsz.Automation.TraceRefinement.
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

Ltac zesu_has_initialized_array_root root spatial :=
  lazymatch spatial with
  | Esnoc ?rest _ ((?address ↦ₘ∗ _)%I) =>
      first [lazymatch address with
             | bv_unsigned ?actualRoot => constr_eq actualRoot root
             | (bv_unsigned ?actualRoot + _)%Z => constr_eq actualRoot root
             end
            | zesu_has_initialized_array_root root rest]
  | Esnoc ?rest _ _ => zesu_has_initialized_array_root root rest
  end.

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

(* Library solvers also call this primitive without passing through the
   project finisher. The call set supplies the timeout switch. *)
Ltac lia ::= zesu_bounded_arithmetic ltac:(Zify.zify; xlia zchecker).
Ltac bv_solve ::= zesu_bounded_arithmetic ltac:(
  bv_simplify_arith;
  bv_saturate_unsigned;
  bv_solve_unfold_tac;
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *;
  simpl; lia).

Ltac zesu_solve_machine_bounds :=
  zesu_bounded_arithmetic ltac:(solve [zesu_normalize_binary_nat_hypotheses;
    zesu_normalize_binary_nat_goal; zesu_normalize_machine_map; bv_solve]).
Ltac zesu_solve_machine_linear :=
  first [zesu_bounded_arithmetic ltac:(zesu_byte_index_arithmetic)
    | zesu_bounded_arithmetic ltac:(first [solve [repeat match goal with
           | Hnat : (_ <= _)%nat |- _ => clear Hnat
           | Hnat : (_ < _)%nat |- _ => clear Hnat
           end; zesu_normalize_machine_map; lia] |
    solve [zesu_normalize_binary_nat_hypotheses;
      zesu_normalize_binary_nat_goal; zesu_normalize_machine_map; lia]])].
(* Preserve the machine normalization used by the existing finisher. *)
Ltac zesu_finish_lia ::= zesu_solve_machine_linear.

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
      first [lazymatch base with
             | bv_add ?root ?displacement => is_var root
             | bv_sub ?root ?displacement => is_var root
             end
            | is_var base;
              lazymatch goal with
              | |- envs_entails ?context _ =>
                  let spatial := eval cbn [env_spatial] in (env_spatial context) in
                  zesu_has_initialized_array_root base spatial
              end];
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

Ltac zesu_tuple_witness T :=
  lazymatch T with
  | li_prod ?A ?B =>
      let head := open_constr:(_ : A) in
      let tail := zesu_tuple_witness B in constr:(li_pair head tail)
  | unit => constr:(tt)
  end.

Create HintDb zesu_payloads.

Ltac zesu_payload_trace requested :=
  lazymatch requested with
  | (spec_trace ?trace ∗ ?rest)%I => constr:(trace)
  | (?other ∗ ?rest)%I => zesu_payload_trace rest
  end.

(* Select payload witnesses only when owned resources and the complete
   payload trace match. Variable types alone do not establish that match. *)
Ltac zesu_match_owned_payload witness body :=
  let requested := eval cbv beta iota zeta delta [li_fst li_snd]
    in (body witness) in
  lazymatch requested with
  | (?resource ∗ ?rest)%I =>
      let trace := zesu_payload_trace rest in
      iSelect resource ltac:(fun Hresource =>
        iMatchHyp ltac:(fun Htrace owned =>
          lazymatch owned with
          | spec_trace ?available =>
              assert_fails (has_evar trace);
              assert_fails (has_evar available);
              first [unify trace available; iExists witness |
                let Hpayload := fresh "Hpayload" in
                assert (Hpayload : trace = available) by
                  (autorewrite with zesu_payloads; reflexivity);
                iEval (rewrite <- Hpayload) in Htrace;
                clear Hpayload; iExists witness |
                let Hrefinement := fresh "HtraceRefinement" in
                assert (Hrefinement : trace ⊆ available) by
                  (autorewrite with zesu_payloads;
                   timeout 2 (zesu_prove_trace_refinement 32%nat));
                iPoseProof (spec_trace_mono available trace Hrefinement
                  with Htrace) as Htrace;
                clear Hrefinement; iExists witness]
          end))
  end.

Ltac zesu_fresh_owned_tuple kind :=
  lazymatch kind with
  | li_prod ?A ?B =>
      let left := zesu_fresh_owned_tuple A in
      let right := zesu_fresh_owned_tuple B in
      constr:((left, right)ₗ)
  | unit => constr:(tt)
  | _ => open_constr:(_ : kind)
  end.

Ltac zesu_match_owned_tuple_atoms requested :=
  lazymatch requested with
  | (?atom ∗ ?rest)%I =>
      first [assert_fails (has_evar atom) |
        iMatchHyp ltac:(fun Howned owned =>
          assert_fails (has_evar owned); unify atom owned)];
      zesu_match_owned_tuple_atoms rest
  | _ => idtac
  end.

Ltac zesu_match_owned_tuple :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod ?A ?B) ?body) =>
      let witness := zesu_fresh_owned_tuple (li_prod A B) in
      let requested := eval cbv beta iota zeta delta [li_fst li_snd] in
        (body witness) in
      zesu_match_owned_tuple_atoms requested;
      assert_fails (has_evar witness);
      iExists witness
  end.

Ltac zesu_open_requested_register_col :=
 lazymatch goal with
 | |- envs_entails _ ((reg_col (?head :: ?rest) ∗ _) %I) =>
     let shapes := constr:(head :: rest) in
     lazymatch shapes with context [ExactShape _] => iEval (rewrite reg_col_cons) end
 | |- envs_entails _ (reg_col (?head :: ?rest)) =>
     let shapes := constr:(head :: rest) in
     lazymatch shapes with context [ExactShape _] => iEval (rewrite reg_col_cons) end
 end.
Ltac zesu_find_owned_exact_register r shapes :=
 lazymatch shapes with
 | ((KindReg r, ExactShape ?value) :: _) => constr:(value)
 | (_ :: ?rest) => zesu_find_owned_exact_register r rest
 end.
Ltac zesu_match_register_witness :=
 lazymatch goal with
 | |- envs_entails _ (@bi_exist _ (li_prod valu unit) ?body) =>
   let requested := eval cbv beta iota zeta delta [li_fst li_snd] in (body (RegVal_Poison, tt)ₗ) in
   lazymatch requested with
   | context [(?r ↦ᵣ RegVal_Poison)%I] =>
     pm_reduce;
     iMatchHyp ltac:(fun Hcol owned =>
       lazymatch owned with
       | reg_col ?shapes => let value := zesu_find_owned_exact_register r shapes in iExists (value, tt)ₗ
       end)
   end
 end.
Ltac zesu_open_owned_return_register :=
 lazymatch goal with
 | |- envs_entails _ ((reg_col ((KindReg ?r, _) :: _) ∗ _) %I) =>
   iMatchHyp ltac:(fun Howned owned =>
    try iEval (rewrite <- reg_mapsto_pred_eq) in Howned;
    let entry := iTypeOf Howned in
    lazymatch entry with
    | Some (_, (r ↦ᵣ: ?body)%I) =>
      iEval (rewrite reg_mapsto_pred_eq) in Howned;
      let value := fresh "returnValue" in
      let Hvalue := iFresh in let Hrest := iFresh in
      let pattern := constr:(IList [[IIdent Hvalue; IIdent Hrest]]) in
      iDestruct Howned as (value) pattern;
      let word := fresh "returnWord" in let Heq := fresh "HreturnValue" in
      iDestruct Hrest as (word) "[%Heq Hrest]"; subst value;
      try zesu_open_return_bundle "Hrest"
    end)
 end.

Ltac zesu_choose_array_tail :=
 lazymatch goal with
 | |- envs_entails _ (@bi_exist _ (li_prod (list (bv 8)) unit) ?body) =>
   let requested := eval cbv beta iota zeta delta [li_fst li_snd] in (body ([], tt)ₗ) in
   lazymatch requested with
   | (⌜_ = take _ (drop ?index ?bytes)⌝ ∗ _)%I =>
     assert_fails (has_evar index); assert_fails (has_evar bytes);
     let Hbound := fresh "HsliceBound" in
     assert (Hbound : (index <= length bytes)%nat) by
       (repeat match goal with Hsrc : ?address = (?base + Z.of_nat ?start)%Z |- context [array_region_start 8 ?base ?address] => rewrite Hsrc byte_array_region_offset end; lia);
     clear Hbound; iExists (drop index bytes, tt)ₗ
   end
 end.
Ltac zesu_solve_array_tail_pure :=
 lazymatch goal with
 | |- envs_entails _ _ => fail
 | |- context [array_region_start 8 _ _] => idtac
 end;
 solve [repeat match goal with Hsrc : ?address = (?base + Z.of_nat ?start)%Z |- context [array_region_start 8 ?base ?address] => rewrite Hsrc byte_array_region_offset end;
   rewrite ?Z.mul_1_l ?length_drop ?take_ge; cbn;
   first [reflexivity | bv_solve | lia]].

Ltac zesu_check_list_bound count fuel :=
  lazymatch count with
  | O => idtac
  | S ?rest => lazymatch fuel with S ?remaining => zesu_check_list_bound rest remaining end
  end.

Ltac zesu_expose_fixed_values values count Hcount :=
  lazymatch count with
  | O => let Heq := fresh "HsavedEquation" in
      destruct values eqn:Heq; [clear Hcount | cbn in Hcount; lia]
  | S ?restCount =>
      let head := fresh "savedValue" in let rest := fresh "savedRest" in
      let Heq := fresh "HsavedEquation" in
      destruct values as [|head rest] eqn:Heq; [cbn in Hcount; lia |];
      cbn in Hcount;
      let Hrest := fresh "HsavedLength" in
      assert (Hrest : length rest = restCount) by lia;
      clear Hcount; zesu_expose_fixed_values rest restCount Hrest
  end.

Ltac zesu_expose_owned_saved_list :=
  multimatch goal with Hcount : length ?values = ?count |- _ =>
    let bound := eval vm_compute in count in
    zesu_check_list_bound bound 16%nat;
    iMatchHyp ltac:(fun Hregisters owned =>
      lazymatch owned with
      | reg_col ?shapes =>
          lazymatch shapes with context [values] =>
            zesu_expose_fixed_values values bound Hcount
          end
      end)
  end.

Ltac zesu_expose_owned_pair_at_call :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec (li_prod (list (bv 8)) unit)) ?body) =>
    let candidate := constr:((fun _ : list seq_label => False, ([] : list (bv 8), tt)ₗ)ₗ) in
    let requested := eval cbv beta iota zeta delta [li_fst li_snd] in (body candidate) in
    lazymatch requested with
    | ((?address ↦ₘ∗ _) ∗ _)%I =>
      assert_fails (has_evar address);
      let source :=
        lazymatch address with
        | bv_unsigned (?base + ?offset)%bv =>
          let delta := eval vm_compute in (bv_unsigned offset) in
          let literal := lazymatch delta with Z0 => constr:(delta) | Zpos _ => constr:(delta) | Zneg _ => constr:(delta) end in
          constr:((bv_unsigned base + literal)%Z)
        | _ => constr:(address)
        end in
      let next :=
        lazymatch source with
        | (?base + ?offset)%Z =>
          let delta := eval vm_compute in (offset + 8)%Z in constr:((base + delta)%Z)
        | _ => constr:((source + 8)%Z)
        end in
      let Hsource := fresh "HsourceAddress" in
      assert (Hsource : (source = address)%Z) by bv_solve;
      let Hnext := fresh "HnextWord" in
      assert (Hnext : (next = source + 8)%Z) by lia;
      let low := open_constr:(_ : bv 64) in
      let high := open_constr:(_ : bv 64) in
      iSelect (source ↦ₘ low)%I ltac:(fun Hlow =>
        iSelect (next ↦ₘ high)%I ltac:(fun Hhigh =>
          assert_fails (has_evar low); assert_fails (has_evar high);
          iEval (try rewrite Hnext) in Hhigh;
          let Hbytes := iFresh in
          iPoseProof (mem_mapsto_u64_pair_to_byte_array source low high) as Hbytes;
          iSpecialize (Hbytes with Hlow);
          iSpecialize (Hbytes with Hhigh);
          let objectBytes := fresh "objectBytes" in
          pose (objectBytes := bv_to_little_endian 8 8 (bv_unsigned low) ++
            bv_to_little_endian 8 8 (bv_unsigned high));
          iEval (fold objectBytes; try rewrite Hsource) in Hbytes;
          clear Hsource Hnext))
    end
  end.

Ltac zesu_infer_owned_payload_tail :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec (li_prod (list ?A) unit)) ?body) =>
    multimatch goal with items : list A |- _ =>
      let tail := open_constr:(_ : spec) in
      let witness := constr:((tail, (items, tt)ₗ)ₗ) in
      let requested := eval cbv beta iota zeta delta [li_fst li_snd] in (body witness) in
      lazymatch requested with
      | (?resource ∗ ?rest)%I =>
        let trace := zesu_payload_trace rest in
        iSelect resource ltac:(fun Hresource =>
          iMatchHyp ltac:(fun Htrace owned =>
            lazymatch owned with
            | spec_trace ?available =>
              assert_fails (has_evar available);
              let Hrefinement := fresh "HtraceRefinement" in
              assert (Hrefinement : trace ⊆ available) by
                (autorewrite with zesu_payloads; try (case_decide; try contradiction; cbn);
                 timeout 2 (zesu_prove_trace_refinement 32%nat));
              assert_fails (has_evar trace);
              assert_fails (has_evar tail);
              iPoseProof (spec_trace_mono available trace Hrefinement with Htrace) as Htrace;
              clear Hrefinement; iExists witness
            end))
      end
    end
  end.

Ltac zesu_match_payload_witness :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec (li_prod (list ?A) unit)) ?body) =>
      multimatch goal with items : list A, tail : spec |- _ =>
        let witness := constr:((tail, (items, tt)ₗ)ₗ) in
        zesu_match_owned_payload witness body
      end
  | |- envs_entails _ (@bi_exist _ (li_prod (list ?A) (li_prod spec unit)) ?body) =>
      multimatch goal with items : list A, tail : spec |- _ =>
        let witness := constr:((items, (tail, tt)ₗ)ₗ) in
        zesu_match_owned_payload witness body
      end
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) ?body) =>
      multimatch goal with tail : spec |- _ =>
        let witness := constr:((tail, tt)ₗ) in
        zesu_match_owned_payload witness body
      end
  end.

Ltac zesu_liInstrPreMatch :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
      let witness := zesu_tuple_witness T in
      let instantiated := eval cbv beta in (body witness) in
      lazymatch instantiated with
      | zesu_instr_pre_match _ _ _ =>
          notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod
      end
  | |- envs_entails _ (zesu_instr_pre_match ?available ?requested _) =>
      first
        [ unify available requested with typeclass_instances;
          notypeclasses refine
            (tac_fast_apply
              (zesu_instr_pre_match_identity _ _ _ eq_refl) _)
        | assert_fails (has_evar requested);
          notypeclasses refine
            (tac_fast_apply (zesu_instr_pre_match_wand _ _ _) _) ]
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

(* Keep a map-bounded current-address witness before Lithium simplifies it. *)
Ltac zesu_preserve_current_unsigned :=
  lazymatch goal with
  | |- bv_unsigned (Z_to_bv 64 ?current) = ?current -> _ =>
          let ramBase := eval cbv [mapRamBase defaultMap] in
            (mapRamBase defaultMap) in
          let ramEnd := eval cbv [machineRamEnd mapRamSize mapRamBase
            defaultMap Z.add] in (machineRamEnd defaultMap) in
          match goal with
          | Hlow : (?lower <= current)%Z,
            Hhigh : (current + ?extent < ?upper)%Z |- _ =>
              let reducedLower := eval cbv [mapRamBase defaultMap] in lower in
              let reducedUpper := eval cbv [machineRamEnd mapRamSize mapRamBase
                defaultMap Z.add] in upper in
              constr_eq reducedLower ramBase;
              constr_eq reducedUpper ramEnd;
              intro H7
          end
  end.

Lemma zesu_masked_register_bool_decide (value mask : bv 64) :
  Z.land (bv_unsigned value) (bv_unsigned mask) = 0 →
  Val_Bool (bool_decide (bv_and value mask = BV 64 0)) = Val_Bool true.
Proof.
  intro Hmask.
  have Hbv : bv_and value mask = BV 64 0 by bv_solve.
  rewrite Hbv bool_decide_true; reflexivity.
Qed.

Lemma zesu_rval_bits_injective n (x y : bv n) :
  RVal_Bits x = RVal_Bits y → x = y.
Proof. intros H. injection H as H. simplify_eq. reflexivity. Qed.

Lemma zesu_val_bits_injective n (x y : bv n) :
  Val_Bits x = Val_Bits y → x = y.
Proof. intros H. injection H as H. simplify_eq. reflexivity. Qed.

Ltac zesu_normalize_rval_bits_equality :=
  match goal with
  | |- RegVal_Base (Val_Bits (bv_to_bvn ?actual)) =
      RegVal_Base (Val_Bits (bv_to_bvn ?expected)) → envs_entails _ _ =>
      is_var actual;
      let H := fresh "Hbits" in
      intro H; apply zesu_rval_bits_injective in H; subst actual
  | |- Val_Bits (bv_to_bvn ?actual) = Val_Bits (bv_to_bvn ?expected)
      → envs_entails _ _ =>
      is_var actual;
      let H := fresh "Hbits" in
      intro H; apply zesu_val_bits_injective in H; subst actual
  | H : Val_Bits (bv_to_bvn ?actual) = Val_Bits (bv_to_bvn ?expected) |- _ =>
      is_var actual;
      apply zesu_val_bits_injective in H; subst actual
  | H : RegVal_Base (Val_Bits (bv_to_bvn ?actual)) = RegVal_Base (Val_Bits (bv_to_bvn ?expected)) |- _ =>
      is_var actual;
      apply zesu_rval_bits_injective in H; subst actual
  | |- envs_entails _ (⌜RegVal_Base (Val_Bits (bv_to_bvn ?actual)) =
      RegVal_Base (Val_Bits (bv_to_bvn ?expected))⌝ -∗ _)%I =>
      is_var actual;
      let H := fresh "Hbits" in
      iIntros (H); apply zesu_rval_bits_injective in H; subst actual
  end.

Ltac zesu_liAStep :=
 liEnsureInvariant;
 try progress (unfold TRACE_LET);
 try liAIntroduceLetInGoal;
 first [
    zesu_normalize_rval_bits_equality
  | zesu_constant_word_array_lookup
  | zesu_constant_word_array_index
  | zesu_open_matching_payload_package
  | zesu_choose_owned_payload_tail
  | zesu_initialized_byte_scratch_tail
  | zesu_normalize_find_mem_address
  | zesu_liAWriteMem
  | zesu_liAReadMem
  | liAAsm
  | liAExp
  | liAOther
  | liUnfoldEarly
  | zesu_liInstrPreMatch
  | zesu_match_payload_witness
  | zesu_match_owned_tuple
  | zesu_expose_owned_saved_list
  | zesu_expose_owned_pair_at_call
  | zesu_infer_owned_payload_tail
  | zesu_close_spec_tail_if_enabled
  | zesu_preserve_current_unsigned
  | liStep
  | liLetBindHint
  | liUnfoldLate
 ]; liSimpl.

Ltac liAStep ::= zesu_liAStep.

(* C1: the trace tail a call returns with.

   The corpus calls this the line every segment proof repeats. A call
   returns with its events still open, so the block is asked for a spec `x`
   with `scons_snap event accept x ⊆ scons event tail`. The witness is
   always the caller's tail, the second argument of the `scons` on the
   right. About 70 proofs and 300 hand lines in the backlog (rows 8, 12,
   13, 16, 18) are this one step.

   Supplying the witness when the existential is opened is not optional.
   Splitting `∃ x : spec *ₗ (), body x` into evars and letting Lithium
   continue does not return: with the spec open, `instr_pre … ?x` matches
   anything in the context. A probe with that rule ran 171 s and was killed
   at its 6 GiB cap, and wired into the automation it took `check-iris`
   past the 200 GiB batch cap twice, against 75 GiB without it. The tail
   does not mention the bound variable, so it reads out from under the
   binder; the inclusion is discharged in the same step, so the search
   never sees a half-instantiated spec. *)
Ltac zesu_close_trace_inclusion :=
  iPureIntro; exact (zesu_scons_snap_subseteq_scons _ _ _).

Ltac zesu_open_trace_exist :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) _) =>
      match goal with
      | |- context [scons _ ?tail] =>
          iExists (tail, tt)ₗ;
          try (iSplit; [zesu_close_trace_inclusion |])
      end
  end.

(* The same step reached as a side condition rather than at the
   existential. The events are compared syntactically and the open spec
   must be an evar: a `unify` on these terms runs a conversion check over
   the whole event history, and the first version did not finish the
   suffix-entry segment in forty minutes. *)
Ltac zesu_finish_trace_tail :=
  lazymatch goal with
  | |- scons_snap ?event _ ?open ⊆ scons ?expected ?tail =>
      is_evar open; constr_eq event expected;
      unify open tail;
      exact (zesu_scons_snap_subseteq_scons _ _ _)
  | |- scons ?event ?open ⊆ scons ?expected ?tail =>
      is_evar open; constr_eq event expected;
      unify open tail;
      exact (zesu_scons_subseteq_scons _ _)
  end.
