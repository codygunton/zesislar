Require Import isla.riscv64.riscv64.
From lithium Require Import proof_state.
From iris.bi Require Import interface.

(* Readiness does not introduce a witness or inspect registered data. *)
Ltac zesu_entry_witness_body_phase fuel body :=
  lazymatch fuel with
  | O => fail 1 "The witness body has too many local aliases."
  | S ?remaining =>
      first [
        (* This match must produce a term that is typed outside the binder. *)
        lazymatch body with
        | (fun _ => ?frame) => let frame_type := type of frame in idtac
        end
      | lazymatch body with
        | (fun _ => @bi_pure _ _) => idtac
        | (fun _ => @bi_sep _ (@bi_pure _ _) ?frame) =>
            let frame_type := type of frame in idtac
        | (fun value => @bi_sep _ (?left value) ?frame) =>
            let frame_type := type of frame in
            zesu_entry_witness_body_phase remaining left
        | (fun value => @bi_sep _ ?frame (?right value)) =>
            let frame_type := type of frame in
            zesu_entry_witness_body_phase remaining right
        | (fun value => @bi_sep _ (?left value) (?right value)) =>
            zesu_entry_witness_body_phase remaining left;
            zesu_entry_witness_body_phase remaining right
        end
      | is_var body;
        let expanded := eval cbv beta iota zeta delta [body LET_ID] in body in
        assert_fails (constr_eq expanded body);
        zesu_entry_witness_body_phase remaining expanded
      | lazymatch body with
        | (fun value => ?head value) =>
            is_var head;
            let expanded := eval cbv beta iota zeta delta [head LET_ID] in body in
            assert_fails (constr_eq expanded body);
            zesu_entry_witness_body_phase remaining expanded
        end]
  end.

Ltac zesu_entry_witness_body_ready body :=
  zesu_entry_witness_body_phase constr:(128%nat) body.
