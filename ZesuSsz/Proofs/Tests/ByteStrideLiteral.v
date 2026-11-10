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
  progress ZesuSsz.Automation2.ResourceGroups.zesu_open_nested_existential_packages.
  assert_fails (idtac; match goal with Hwidth : (8 = ?stride * 8)%N |- _ => is_var stride end).
  iMatchHyp ltac:(fun H body =>
    lazymatch body with big_opL _ _ (_ :: _) => iEval (simpl) in H end).
  ZesuSsz.Automation2.ResourceGroups.zesu_open_resource_groups.
  iFrame "HR".
  rewrite <- isla.ghost_state.mem_mapsto_array_eq.
  ZesuSsz.Automation2.ByteArrayAssemblyCodec.zesu_byte_array_assemble_codec.
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
  progress ZesuSsz.Automation2.ResourceGroups.zesu_open_nested_existential_packages.
  zesu_block2.
Qed.

Print Assumptions frame_cells_rebuild_for_successor.

(* The context owns the saved frame as two 64-bit word cells, and the
   successor entry asks for the same 16 bytes as one array. The word addresses
   equal the array base and the base plus 8 only after wrapped 64-bit
   arithmetic: one through a local definition, one in wrap-normalized form.
   The core places both words and rebuilds the array from their bytes. *)
Lemma frame_words_rebuild_for_successor `{!islaG Sigma} `{!threadG}
    (X C : bv 64) (x : Z) (w0 w1 : bv 64) (R : iProp Sigma) :
  bv_unsigned C = 2^64 - 16 -> bv_unsigned X = x -> 16 <= x ->
  let L := (X + C)%bv in
  R -∗
  bv_unsigned L ↦ₘ w0 -∗
  (x + (bv_unsigned C + bv_unsigned (BV 64 8) - bv_modulus 64)) ↦ₘ w1 -∗
  (isla.ghost_state.mem_mapsto_array_def (x - 16) (DfracOwn 1)
      (Z_to_bv 8 (Z.land (bv_unsigned w0) (Z.ones 8)) ::
       Z_to_bv 8 (Z.land (bv_unsigned w0 ≫ 8) (Z.ones 8)) ::
       Z_to_bv 8 (Z.land (bv_unsigned w0 ≫ 16) (Z.ones 8)) ::
       Z_to_bv 8 (Z.land (bv_unsigned w0 ≫ 24) (Z.ones 8)) ::
       Z_to_bv 8 (Z.land (bv_unsigned w0 ≫ 32) (Z.ones 8)) ::
       Z_to_bv 8 (Z.land (bv_unsigned w0 ≫ 40) (Z.ones 8)) ::
       Z_to_bv 8 (Z.land (bv_unsigned w0 ≫ 48) (Z.ones 8)) ::
       Z_to_bv 8 (Z.land (bv_unsigned w0 ≫ 56) (Z.ones 8)) ::
       bv_to_little_endian 8 8 (bv_unsigned w1)) ∗ R).
Proof.
  intros HC HX Hx L. iIntros "HR H0 H1".
  zesu_block2.
Qed.

Print Assumptions frame_words_rebuild_for_successor.

(* Late split: each saved word is still one unopened byte array when the
   successor first asks for the frame, so the rebuild step finds no cells.
   The package opener then splits the words into chains of byte cells at the
   same wrapped addresses, and the core rebuilds the array from those cells. *)
Lemma frame_words_late_split_for_successor `{!islaG Sigma} `{!threadG}
    (X C : bv 64) (x : Z) (w0 w1 : bv 64) (R : iProp Sigma) :
  bv_unsigned C = 2^64 - 16 -> bv_unsigned X = x -> 16 <= x ->
  let L := (X + C)%bv in
  R -∗
  isla.ghost_state.mem_mapsto_array_def (bv_unsigned L) (DfracOwn 1)
    (bv_to_little_endian 8 8 (bv_unsigned w0)) -∗
  isla.ghost_state.mem_mapsto_array_def
    (x + (bv_unsigned C + bv_unsigned (BV 64 8) - bv_modulus 64)) (DfracOwn 1)
    (bv_to_little_endian 8 8 (bv_unsigned w1)) -∗
  (isla.ghost_state.mem_mapsto_array_def (x - 16) (DfracOwn 1)
      (bv_to_little_endian 8 8 (bv_unsigned w0) ++
       bv_to_little_endian 8 8 (bv_unsigned w1)) ∗ R).
Proof.
  intros HC HX Hx L. iIntros "HR H0 H1".
  Fail ZesuSsz.Automation2.ByteArrayAssemblyCodec.zesu_byte_array_rebuild_requested.
  progress ZesuSsz.Automation2.ResourceGroups.zesu_open_nested_existential_packages.
  zesu_block2.
Qed.

Print Assumptions frame_words_late_split_for_successor.
