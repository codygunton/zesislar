(* A loop cursor is a register word R with a retained equation
   `bv_unsigned R = T`, where T contains the root of an owned array and a
   symbolic offset. The closed-offset array rules cannot see the root in the
   address `bv_unsigned R`, and the region-fault rules cannot see the array
   range of R. This module derives `root <= bv_unsigned R < root + extent`
   once per path from selected facts, and looks up a load or store at the
   address T. It names no address, offset, register, or contract predicate. *)
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.ResourceGroups.
Require Import ZesuSsz.Automation2.ContextCollection.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.SearchBudget.
Require Import ZesuSsz.Automation2.VmClosed.
From iris.proofmode Require Import environments.
From stdpp Require Import bitvector.definitions bitvector.tactics.
From Coq Require Import ZArith.ZArith Lia.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

(* The range derivation ran for this register on this path. *)
Polymorphic Inductive zesu_register_cursor_attempted {A : Type} (register : A) : Prop :=
  zesu_register_cursor_token : zesu_register_cursor_attempted register.

(* Find a retained conjunct `bv_unsigned register = target`. *)
Ltac zesu_cursor_conjunct register proof statement continuation :=
  lazymatch statement with
  | ?left /\ ?right =>
      first [zesu_cursor_conjunct register constr:(@proj1 left right proof) left continuation |
             zesu_cursor_conjunct register constr:(@proj2 left right proof) right continuation]
  | bv_unsigned register = ?target =>
      lazymatch target with context [register] => fail | _ => continuation proof target end
  end.

Ltac zesu_cursor_equation register continuation :=
  match goal with
  | H : ?statement |- _ =>
      lazymatch type of statement with Prop => idtac end;
      zesu_cursor_conjunct register H statement continuation
  end.

(* Select an owned array whose root occurs in the equation's target. *)
Ltac zesu_cursor_array target continuation :=
  zesu_expose_environment_alias;
  iMatchHyp ltac:(fun _ body =>
    lazymatch body with
    | @mem_mapsto_array _ _ ?width ?lower _ ?values =>
        assert_fails (has_evar lower); assert_fails (has_evar values);
        lazymatch target with context [lower] => continuation width lower values end
    end).

Ltac zesu_cursor_extent width values :=
  let stride := eval vm_compute in (Z.of_N (width `div` 8)) in
  lazymatch stride with
  | 1 => constr:(Z.of_nat (length values))
  | _ => constr:(Z.of_nat (length values) * stride)
  end.

Ltac zesu_cursor_arithmetic statement :=
  lazymatch statement with
  | @eq Z _ _ => idtac | Z.le _ _ => idtac | Z.lt _ _ => idtac
  | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | ~ ?inner => zesu_cursor_arithmetic inner
  | ?left /\ ?right => zesu_cursor_arithmetic left; zesu_cursor_arithmetic right
  | ?left \/ ?right => zesu_cursor_arithmetic left; zesu_cursor_arithmetic right
  end.

(* A low mask keeps the residue modulo a power of two. *)
Lemma zesu_cursor_low_mask (width bits : N) (word mask : bv width) :
  bv_unsigned mask = Z.ones (Z.of_N bits) ->
  bv_unsigned (bv_and word mask) = bv_unsigned word mod 2 ^ Z.of_N bits.
Proof. intros Hmask. rewrite bv_and_unsigned Hmask Z.land_ones; [reflexivity | lia]. Qed.

Ltac zesu_cursor_low_masks :=
  repeat match goal with
  | |- context [@bv_unsigned ?width (bv_and ?word ?mask)] =>
      VmClosed.zesu_vm_closed mask;
      let value := eval vm_compute in (bv_unsigned mask) in
      let bits := eval vm_compute in (Z.to_N (Z.log2 (value + 1))) in
      let Hmask := fresh "HcursorMask" in
      assert (Hmask : bv_unsigned mask = Z.ones (Z.of_N bits)) by (vm_compute; reflexivity);
      rewrite (zesu_cursor_low_mask width bits word mask Hmask); clear Hmask
  end.

(* Evaluate closed signed and unsigned views of literals. *)
Ltac zesu_cursor_closed_views :=
  repeat match goal with
  | |- context [@bv_signed ?width ?word] =>
      VmClosed.zesu_vm_closed word;
      let value := eval vm_compute in (@bv_signed width word) in
      change (@bv_signed width word) with value
  | |- context [@bv_unsigned ?width ?word] =>
      lazymatch word with BV _ _ => fail | Z_to_bv _ _ => fail | _ => idtac end;
      VmClosed.zesu_vm_closed word;
      let value := eval vm_compute in (@bv_unsigned width word) in
      change (@bv_unsigned width word) with value
  end.

(* Name each unsigned value that is not a sum, a cast, a low mask, or a
   literal. Its range is the only fact the linear solver needs about it. *)
Ltac zesu_cursor_unsigned_atoms :=
  repeat match goal with H : context [@bv_unsigned _ _] |- _ => revert H end;
  rewrite ?bv_add_unsigned ?bv_sub_unsigned;
  repeat (progress zesu_cursor_low_masks; rewrite ?bv_add_unsigned ?bv_sub_unsigned);
  zesu_cursor_closed_views;
  repeat match goal with
  | |- context [@bv_unsigned ?width ?word] =>
      tryif is_var word then fail else
      lazymatch word with
      | bv_add _ _ => fail | bv_sub _ _ => fail | Z_to_bv _ _ => fail | BV _ _ => fail
      | _ => idtac
      end;
      let Hrange := fresh "HcursorAtomRange" in
      pose proof (bv_unsigned_in_range width word) as Hrange;
      let atom := fresh "cursorAtom" in
      set (atom := bv_unsigned word) in *; clearbody atom
  end;
  rewrite ?Z_to_bv_unsigned ?bv_unsigned_BV; intros.

Ltac zesu_cursor_linear :=
  repeat match goal with
  | H : ?statement |- _ =>
      lazymatch type of statement with Prop => idtac end;
      tryif zesu_cursor_arithmetic statement then fail else clear H
  end;
  zesu_cursor_unsigned_atoms;
  bv_saturate_unsigned;
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *;
  simpl;
  lia.

(* Expose loop binders at their carrier type, retained conjunctions, guards,
   and widened comparisons as integer facts. Solve with the facts the goal
   reaches. *)
Ltac zesu_cursor_expose_facts :=
  repeat match goal with
  | value : lvar _ ?carrier |- _ => change carrier in value
  end;
  repeat first [progress zesu_split_folded_pure |
    match goal with H : _ /\ _ |- _ => destruct H end];
  repeat match goal with
  | H : negb (bool_decide _) = true |- _ => apply negb_true_iff, bool_decide_eq_false in H
  | H : bool_decide _ = true |- _ => apply bool_decide_eq_true in H
  end;
  repeat match goal with
  | H : context [bv_signed (@bv_zero_extend 64 128 ?word)] |- _ =>
      rewrite (zesu_signed_zero_extend_64_128 word) in H
  end;
  repeat match goal with
  | H : @eq (bv _) _ _ |- _ => apply (f_equal bv_unsigned) in H
  | H : ~ (@eq (bv _) _ _) |- _ => apply bv_neq in H
  end.

Ltac zesu_cursor_range_solve :=
  zesu_cursor_expose_facts;
  ContextCollection.zesu_solve_goal_selected ("register_array_cursor"%string)
    ltac:(zesu_cursor_linear).

(* A loop step relates the index to the cursor, the limit, and the guards
   behind the limit, so its facts lie up to four shared-term rounds away. *)
Ltac zesu_cursor_step_solve :=
  zesu_cursor_expose_facts;
  solve [once ltac2:(ZesuSsz.Automation2.ContextCollection.zesu_select_goal_facts 4 48 2048);
    SearchBudget.zesu_solve_selected ("register_array_cursor.step"%string)
      ltac:(zesu_cursor_linear)].

(* Add the cursor range once per register and path. A failed derivation
   leaves only the marker, so later steps do not repeat it. *)
Ltac zesu_register_cursor_range register :=
  assert_fails (has_evar register);
  lazymatch type of register with bv _ => idtac end;
  assert_fails (idtac; match goal with
    | _ : zesu_register_cursor_attempted register |- _ => idtac end);
  let marker := fresh "HcursorAttempted" in
  pose proof (zesu_register_cursor_token register) as marker;
  try (zesu_cursor_equation register ltac:(fun equation target =>
    zesu_cursor_array target ltac:(fun width lower values =>
      let extent := zesu_cursor_extent width values in
      let Hrange := fresh "HcursorRange" in
      assert (Hrange : lower <= bv_unsigned register < lower + extent) by
        (clear marker; zesu_cursor_range_solve)))).

(* Follow local definitions and zero offsets to the register word. *)
Ltac zesu_cursor_register word continuation :=
  lazymatch word with
  | bv_add ?inner _ => zesu_cursor_register inner continuation
  | _ =>
      is_var word;
      tryif (idtac; match goal with local := _ |- _ => constr_eq local word end)
      then (match goal with
        | local := ?body |- _ => constr_eq local word; zesu_cursor_register body continuation
        end)
      else continuation word
  end.

Ltac zesu_cursor_widened_word expression continuation :=
  first [
    match expression with
    | context [@bv_zero_extend 64 128 ?word] => zesu_cursor_register word continuation
    end
  | match goal with
    | local := ?body |- _ =>
        lazymatch expression with context [local] =>
          match body with
          | context [@bv_zero_extend 64 128 ?word] => zesu_cursor_register word continuation
          end
        end
    end].

(* A region assertion widens the address word. Derive the cursor range
   before the region-fault rules read the assertion. *)
Ltac zesu_register_cursor_assert :=
  lazymatch goal with
  | |- envs_entails _ ?target =>
      let expression := lazymatch target with
        | WPasm (Smt (Assert ?expression) _ :t: _) => expression
        | (WPasm (Smt (Assert ?expression) _ :t: _) ∧ True)%I => expression
        end in
      zesu_cursor_widened_word expression ltac:(fun register =>
        zesu_register_cursor_range register)
  end.

(* A load or store at a cursor uses the equation's integer address. The
   array rules then see the root and the range proves the index bound. *)
Ltac zesu_register_array_address :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo (bv_unsigned ?register)) _) =>
      is_var register;
      first [
        match goal with
        | Hcursor : ?lower <= bv_unsigned register < _ |- _ =>
            zesu_cursor_equation register ltac:(fun equation target =>
              zesu_cursor_array target ltac:(fun width lower' values =>
                constr_eq lower lower';
                let Hrange := fresh "HarrayAddressRange" in
                let stride := eval vm_compute in (Z.of_N (width `div` 8)) in
                assert (Hrange : (lower <= target < lower +
                  Z.of_nat (length values) * Z.of_N (width `div` 8))%Z) by
                  (let Hequation := fresh "HcursorEquation" in
                   pose proof equation as Hequation;
                   clear - Hcursor Hequation; rewrite <- Hequation;
                   change (Z.of_N (width `div` 8)) with stride; lia);
                rewrite equation))
        end
      | zesu_register_cursor_range register]
  end.

Ltac zesu_register_cursor_step :=
  first [zesu_register_array_address | zesu_register_cursor_assert].
