Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The package opener unfolds a saved-frame byte array into its width equation
   8 = len * 8 and one cell per byte. It must fix len to 1, so the existing
   assembler rebuilds the same array from the cells. *)
Lemma byte_array_cells_rebuild `{!islaG Sigma} `{!threadG} (a : Z)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : bv 8) (R : iProp Sigma) :
  R -∗
  isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15] -∗
  (isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15] ∗ R).
Proof.
  iIntros "HR Harray".
  progress ResourceGroups.zesu_open_nested_existential_packages.
  assert_fails (idtac; match goal with Hwidth : (8 = ?stride * 8)%N |- _ => is_var stride end).
  iMatchHyp ltac:(fun H body =>
    lazymatch body with big_opL _ _ (_ :: _) => iEval (simpl) in H end).
  ResourceGroups.zesu_open_resource_groups.
  iFrame "HR".
  rewrite <- isla.ghost_state.mem_mapsto_array_eq.
  ByteArrayAssemblyCodec.zesu_byte_array_assemble_codec.
Qed.

Print Assumptions byte_array_cells_rebuild.

(* The current entry owns the saved frame as one array, an earlier step opened
   it into byte cells, and the successor entry asks for the same array. The
   core rebuilds the array from the cells and keeps the other resources. *)
Lemma frame_cells_rebuild_for_successor `{!islaG Sigma} `{!threadG} (sp : Z)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : bv 8) (R : iProp Sigma) :
  R -∗
  isla.ghost_state.mem_mapsto_array_def (sp - 16) (DfracOwn 1) [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15] -∗
  (∃ x : Z, ⌜x = sp⌝ ∗
    isla.ghost_state.mem_mapsto_array_def (x - 16) (DfracOwn 1) [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15] ∗ R).
Proof.
  iIntros "HR Hframe".
  progress ResourceGroups.zesu_open_nested_existential_packages.
  zesu_block2.
Qed.

Print Assumptions frame_cells_rebuild_for_successor.
