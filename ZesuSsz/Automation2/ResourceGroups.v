Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
From iris.proofmode Require Import environments.
From Coq Require Import NArith Lia.

(* Pure extraction removes its persistent source. Separation keeps both children. *)
Ltac zesu_expose_environment_alias :=
  repeat match goal with
  | Hlocal := _ : envs (iPropI _) |- envs_entails ?current _ =>
      constr_eq Hlocal current; subst Hlocal
  end.

Ltac zesu_open_resource_groups :=
  repeat iMatchHyp ltac:(fun H body =>
    lazymatch body with
    | (_ ∗ _)%I => iDestruct H as "[? ?]"
    | (⌜_⌝)%I => iDestruct H as %?; try iClear H
    end).

(* Split an instruction bundle only when its first PC is requested. *)
Ltac zesu_open_requested_instr_bundle :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindInstrKind ?address _) _) =>
      iMatchHyp ltac:(fun H body =>
        lazymatch body with
        | (instr ?firstAddress _ ∗ _)%I =>
            constr_eq firstAddress address;
            iDestruct H as "[? ?]"
        end)
  end.

(* Unfold only a package whose first resource is the current goal resource. *)
Ltac zesu_open_matching_resource_package :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (?requested ∗ _)%I =>
      iMatchHyp ltac:(fun H body =>
        let head := get_head body in
        tryif first [constr_eq head constr:(@bi_sep) |
                     constr_eq head constr:(@bi_pure)] then fail else
          let expanded := eval cbv beta delta [head] in body in
          lazymatch expanded with
          | (?first ∗ _)%I =>
              constr_eq first requested;
              progress iEval (unfold head) in H;
              iDestruct H as "[? ?]"
          end)
  end.

(* Open existential resources without choosing or discarding their witnesses. *)
Ltac zesu_contains_existential_resource body :=
  lazymatch body with
  | @bi_exist _ _ _ => idtac
  | (?left ∗ ?right)%I =>
      first [zesu_contains_existential_resource left |
             zesu_contains_existential_resource right]
  | _ =>
      let head := get_head body in
      let registered := constr:(_ : LithiumUnfold head) in
      let expanded := eval cbv beta zeta delta [head] in body in
      tryif constr_eq expanded body then fail else
        zesu_contains_existential_resource expanded
  end.

Ltac zesu_open_existential_package_step :=
  first [
    progress iMatchHyp ltac:(fun H body =>
      lazymatch body with
      | @bi_exist _ _ _ => iDestruct H as (?) H
      end)
  | progress iMatchHyp ltac:(fun H body =>
      lazymatch body with
      | (_ ∗ _)%I => zesu_contains_existential_resource body;
          iDestruct H as "[? ?]"
      end)
  | progress iMatchHyp ltac:(fun H body =>
      let head := get_head body in
      tryif first [constr_eq head constr:(@bi_sep) |
                   constr_eq head constr:(@bi_pure) |
                   constr_eq head constr:(@bi_exist)] then fail else idtac;
      let expanded := eval cbv beta zeta delta [head] in body in
      zesu_contains_existential_resource expanded;
      progress iEval (unfold head) in H;
      zesu_open_resource_groups)
  ].

(* An opened byte array `mem_mapsto_array_def` leaves its width equation
   8 = len * 8 and cells at a + i * Z.of_N len. Fix len to 1 at once, so the
   cells carry the literal stride that the array rebuild rules expect. *)
Lemma zesu_byte_stride_one (stride : N) : (8 = stride * 8)%N -> stride = 1%N.
Proof. lia. Qed.

Ltac zesu_byte_stride_literal :=
  repeat multimatch goal with
  | Hwidth : (8 = ?stride * 8)%N |- _ =>
      is_var stride;
      pose proof (zesu_byte_stride_one stride Hwidth);
      subst stride
  end.

Ltac zesu_open_nested_existential_packages :=
  zesu_open_existential_package_step;
  repeat zesu_open_existential_package_step;
  zesu_open_resource_groups;
  zesu_byte_stride_literal.

(* Preserve every package component before selecting the requested field. *)
Ltac zesu_open_requested_struct_sys_package :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindStructRegMapsTo _ _) _) =>
      progress zesu_open_nested_existential_packages
  end.

(* Branch frames preserve x9 behind their transparent common frame. *)
Ltac zesu_open_requested_saved_x9_package :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindRegMapsTo "x9") _) =>
      iMatchHyp ltac:(fun H body =>
        let outerHead := get_head body in
        tryif first [constr_eq outerHead constr:(@bi_sep) |
                     constr_eq outerHead constr:(@bi_pure)] then fail else
          let outer := eval cbv beta zeta delta [outerHead] in body in
          let innerHead := get_head outer in
          let inner := eval cbv beta zeta delta [innerHead] in outer in
          lazymatch inner with
          | (reg_col ?other ∗ reg_col ?saved ∗ reg_col ?global ∗
              "x8" ↦ᵣ RVal_Bits ?old8 ∗ "x9" ↦ᵣ RVal_Bits ?old9 ∗ _)%I =>
              constr_eq global constr:(
                [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)]);
              progress iEval (unfold outerHead) in H;
              progress iEval (unfold innerHead) in H;
              iDestruct H as "[? ?]";
              zesu_open_resource_groups
          end)
  end.

(* Match the requested first frame resource through two transparent heads. *)
Ltac zesu_open_matching_two_level_frame :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (?requested ∗ _)%I =>
      lazymatch requested with
      | reg_col _ =>
      iMatchHyp ltac:(fun H body =>
        let outerHead := get_head body in
        tryif first [constr_eq outerHead constr:(@bi_sep) |
                     constr_eq outerHead constr:(@bi_pure)] then fail else
          let outer := eval cbv beta zeta delta [outerHead] in body in
          let innerHead := get_head outer in
          tryif first [constr_eq innerHead constr:(@bi_sep) |
                       constr_eq innerHead constr:(@bi_pure)] then fail else
            let inner := eval cbv beta zeta delta [innerHead] in outer in
            lazymatch inner with
            | (?first ∗ _)%I =>
                constr_eq first requested;
                progress iEval (unfold outerHead) in H;
                progress iEval (unfold innerHead) in H;
                iDestruct H as "[? ?]"
            end)
      end
  end.

Ltac zesu_is_pure_resource body :=
  lazymatch body with
  | (bi_pure _)%I => idtac
  | (?left ∗ ?right)%I =>
      zesu_is_pure_resource left; zesu_is_pure_resource right
  end.

(* Take an exact pure descriptor fact while retaining its array owner. *)
Ltac zesu_extract_descriptor_pure requested :=
  iMatchHyp ltac:(fun H body =>
    let head := get_head body in
    tryif first [constr_eq head constr:(@bi_sep) |
                 constr_eq head constr:(@bi_pure)] then fail else
      let unfolded := eval cbv beta zeta delta [head] in body in
      lazymatch unfolded with
      | (?array ∗ ⌜?actual⌝)%I =>
          lazymatch array with
          | (_ ↦ₘ∗ _)%I =>
              constr_eq actual requested;
              progress iEval (unfold head) in H;
              iDestruct H as "[? ?]";
              zesu_open_resource_groups
          end
      end).

Ltac zesu_extract_matching_descriptor_pure :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (⌜?requested⌝)%I =>
      zesu_extract_descriptor_pure requested
  | |- envs_entails _ (⌜?requested⌝ ∗ _)%I =>
      zesu_extract_descriptor_pure requested
  end.

Ltac zesu_finish_pure_resources :=
  lazymatch goal with
  | |- envs_entails _ ?body =>
      zesu_is_pure_resource body;
      solve [repeat first
        [solve [iPureIntro; assumption] | solve [done] | iSplit |
         solve [iPureIntro; first [lia | bv_solve]]]]
  end.
