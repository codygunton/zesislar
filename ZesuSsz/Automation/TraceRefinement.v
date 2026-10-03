Require Import isla.isla.

Lemma zesu_scons_trace_refinement event tail1 tail2 :
  tail1 ⊆ tail2 -> scons event tail1 ⊆ scons event tail2.
Proof. intros Htail. spec_solver. Qed.

Lemma zesu_snapshot_trace_refinement event accept tail1 tail2 :
  tail1 ⊆ tail2 -> scons_snap event accept tail1 ⊆ scons event tail2.
Proof. intros Htail. spec_solver. Qed.

Ltac zesu_prove_trace_refinement fuel :=
  first [reflexivity | lazymatch fuel with
  | S ?rest =>
      lazymatch goal with
      | |- scons _ _ ⊆ scons _ _ =>
          apply zesu_scons_trace_refinement; zesu_prove_trace_refinement rest
      | |- scons_snap _ _ _ ⊆ scons _ _ =>
          apply zesu_snapshot_trace_refinement; zesu_prove_trace_refinement rest
      | |- ?left ⊆ ?right =>
          first [let head := get_head left in
                  lazymatch head with scons => fail | scons_snap => fail | _ => progress unfold head end
                |let head := get_head right in
                  lazymatch head with scons => fail | scons_snap => fail | _ => progress unfold head end];
          zesu_prove_trace_refinement rest
      end
  end].
