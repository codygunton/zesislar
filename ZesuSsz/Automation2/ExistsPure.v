From iris.proofmode Require Import proofmode environments.
From lithium Require Import pure_definitions.
Set Default Proof Mode "Classic".

(* A leftover existential whose witnesses only pure facts constrain.

   The block automation can end on `∃ x, ⌜P1 x⌝ ∗ ... ∗ ⌜Pn x⌝ ∗ R` where
   the spatial part R does not mention x and every resource of R is held
   (a history restatement at a loop head, say). Its open part is the pure
   statement `∃ x1 ... xk, P1 x ∧ ... ∧ Pn x`, the components of a
   tuple-typed witness bound one by one. The residual export
   (`Diagnostics.zesu_diag_export_final`) exports that statement, and the
   block's last stage (`Finish.zesu_block2`) closes the goal from a residual
   lemma for it (`zesu_exists_pure_residual`): the witnesses and facts come
   from the lemma, the held resources are framed. Syntactic only: a body
   with any other shape is refused. *)

(* The pure conjuncts of a separating conjunction (`True` when none). *)
Ltac zesu_ep_pure_of R :=
  lazymatch R with
  | bi_sep ?A ?B =>
      let a := zesu_ep_pure_of A in
      let b := zesu_ep_pure_of B in
      lazymatch a with
      | True => b
      | _ => lazymatch b with True => a | _ => constr:(a /\ b) end
      end
  | bi_pure ?P => P
  | _ => constr:(True)
  end.

(* The spatial conjuncts of a separating conjunction, pure ones replaced by
   `⌜True⌝`. *)
Ltac zesu_ep_spatial_of R :=
  lazymatch R with
  | bi_sep ?A ?B =>
      let a := zesu_ep_spatial_of A in
      let b := zesu_ep_spatial_of B in
      lazymatch a with
      | bi_pure True => b
      | _ => lazymatch b with bi_pure True => a | _ => constr:(bi_sep a b) end
      end
  | @bi_pure ?PROP _ => constr:(@bi_pure PROP True)
  | _ => R
  end.

(* `∃ a1 ... ak, P (a1, ..., ak)` for a witness type `A1 *ₗ ... *ₗ Ak *ₗ ()`;
   a type that is not a tuple gets one binder. *)
Ltac zesu_ep_exists T P :=
  lazymatch T with
  | li_prod ?A ?B =>
      let a := fresh "zesu_w" in
      let b := fresh "zesu_w" in
      constr:(exists a : A, ltac:(
        let Q := constr:(fun b : B => P (li_pair a b)) in
        let r := zesu_ep_exists B Q in exact r))
  | unit => constr:(P tt)
  | _ => let a := fresh "zesu_w" in constr:(exists a : T, P a)
  end.

(* Every spatial conjunct of S is a held resource, syntactically. *)
Ltac zesu_ep_held S :=
  lazymatch S with
  | bi_sep ?A ?B => zesu_ep_held A; zesu_ep_held B
  | bi_pure True => idtac
  | _ => iMatchHyp ltac:(fun _ R => constr_eq R S)
  end.

(* On `envs_entails Δ (∃ x : T, body x)` of the shape above: `k E` with E
   the pure statement. Fails on any other shape, on a spatial part that
   mentions the witness or is not held, and when no pure conjunct mentions
   the witness. *)
Ltac zesu_exists_pure_parts k :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
      let x := fresh "zesu_x" in
      let Sf := constr:(fun x : T => ltac:(
        let b := eval cbv beta in (body x) in
        let s := zesu_ep_spatial_of b in
        lazymatch s with context [x] => fail | _ => exact s end)) in
      let S := lazymatch Sf with (fun _ => ?S) => S end in
      let Pf := constr:(fun x : T => ltac:(
        let b := eval cbv beta in (body x) in
        let p := zesu_ep_pure_of b in
        lazymatch p with context [x] => exact p end)) in
      zesu_ep_held S;
      let E := zesu_ep_exists T Pf in
      let E := eval cbv beta iota delta [li_fst li_snd] in E in
      k E
  end.

(* The witness of a proof H of `zesu_ep_exists T P`, destructed. *)
Ltac zesu_ep_witness T H k :=
  lazymatch T with
  | li_prod ?A ?B =>
      let a := fresh "zesu_ex" in
      destruct H as [a H];
      zesu_ep_witness B H ltac:(fun w => k constr:(li_pair a w))
  | unit => k constr:(tt)
  | _ => let a := fresh "zesu_ex" in destruct H as [a H]; k a
  end.

(* Closes the goal from `close E`, a tactic that proves the pure statement
   (a residual lemma). *)
Ltac zesu_exists_pure_close close :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T _) =>
      zesu_exists_pure_parts ltac:(fun E =>
        let H := fresh "HexistsPure" in
        assert (H : E) by close;
        zesu_ep_witness T H ltac:(fun w =>
          iExists w;
          cbv beta iota delta [li_fst li_snd];
          repeat match type of H with _ /\ _ =>
            let H1 := fresh "HexistsPure" in destruct H as [H1 H] end;
          iFrame;
          try (iPureIntro; repeat split; first [assumption | exact I])))
  end.
