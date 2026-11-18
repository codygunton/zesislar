From Coq Require Import ZArith String.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.

(* A literal PC selects the source declaration without the context-wide
   closedness check; a PC behind a local name still takes it. *)
#[local] Instance source_declaration_key_test :
  ZesuSsz.Automation2.SourceWitnessInputs.ZesuSourceDeclaration
    (BV 64 4096) 3%Z 64%N "declared"%string := I.

Goal True.
Proof.
  pose (pc := Z_to_bv 64 4096).
  ZesuSsz.Automation2.SourceWitnessInputs.zesu_read_source_declaration_key
    constr:(pc) constr:(3%Z) constr:(64%N)
    ltac:(fun key => constr_eq key "declared"%string).
  exact I.
Qed.

#[local] Ltac ZesuSsz.Automation2.VmClosed.zesu_closed_term term ::=
  fail "context-wide closedness check".

Goal True.
Proof.
  ZesuSsz.Automation2.SourceWitnessInputs.zesu_read_source_declaration_key
    constr:(Z_to_bv 64 4096) constr:(3%Z) constr:(64%N)
    ltac:(fun key => constr_eq key "declared"%string).
  pose (pc := Z_to_bv 64 4096).
  Fail ZesuSsz.Automation2.SourceWitnessInputs.zesu_read_source_declaration_key
    constr:(pc) constr:(3%Z) constr:(64%N) ltac:(fun key => idtac).
  exact I.
Qed.
