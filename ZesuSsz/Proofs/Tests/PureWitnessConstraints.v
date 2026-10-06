Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Record WitnessAnchor := { witnessAnchorTag : Z }.

Lemma pure_constraints_opt_in : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepPureWitnessConstraints) in idtac.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.PureWitnessConstraints.

Definition witnessConstraintResources `{!islaG Sigma} `{!threadG}
    (anchor : WitnessAnchor) (P : WitnessAnchor -> Z -> Z -> Prop)
    (R : Z -> Z -> iProp Sigma) (n i : Z) : iProp Sigma :=
  (⌜P anchor n i⌝ ∗ R n i)%I.

Lemma pure_constraints_ordered `{!islaG Sigma} `{!threadG}
    (anchor : WitnessAnchor) (P : WitnessAnchor -> Z -> Z -> Prop)
    (R : Z -> Z -> iProp Sigma) (n i unrelated : Z)
    (Howned : P anchor n i) :
  R n i -∗ (∃ next_n next_i : Z,
    witnessConstraintResources anchor P R next_n next_i)%I.
Proof.
  iStartProof. iIntros "HR".
  zesu_pure_witness_constraints_if_enabled.
  iFrame. done.
Qed.

Definition witnessRoleResources `{!islaG Sigma} `{!threadG}
    (anchor : WitnessAnchor)
    (P : WitnessAnchor -> Z -> Z -> Z -> list byte -> Prop)
    (F : WitnessAnchor -> list byte -> Prop)
    (R : Z -> Z -> Z -> list byte -> list byte -> bv 64 -> iProp Sigma)
    (n i cursor : Z) (bytes frame : list byte) (loaded : bv 64) : iProp Sigma :=
  (⌜P anchor n i cursor bytes /\ F anchor frame⌝ ∗
   R n i cursor bytes frame loaded)%I.

Lemma pure_constraints_distinct_roles `{!islaG Sigma} `{!threadG}
    (anchor : WitnessAnchor)
    (P : WitnessAnchor -> Z -> Z -> Z -> list byte -> Prop)
    (F : WitnessAnchor -> list byte -> Prop)
    (R : Z -> Z -> Z -> list byte -> list byte -> bv 64 -> iProp Sigma)
    (n i cursor unrelated : Z) (bytes frame unrelated_bytes : list byte)
    (loaded : bv 64) (Hfold : P anchor n i cursor bytes)
    (Hframe : F anchor frame) :
  R n i cursor bytes frame loaded -∗
  (∃ (next_n next_i next_cursor : Z) (next_bytes next_frame : list byte)
      (next_loaded : bv 64),
    witnessRoleResources anchor P F R next_n next_i next_cursor
      next_bytes next_frame next_loaded)%I.
Proof.
  iStartProof. iIntros "HR".
  zesu_pure_witness_constraints_if_enabled.
  iFrame. done.
Qed.

Lemma pure_constraints_structural_goal : True.
Proof.
  Fail zesu_pure_witness_constraints_if_enabled.
  exact I.
Qed.
