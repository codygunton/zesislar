Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.

Record IntegerAddressArgs := { integerAddressBase : Z }.
Definition integerAddressDomain (args : IntegerAddressArgs) (bytes : list (bv 8)) :=
  (0 <= integerAddressBase args /\ integerAddressBase args + 40 < 2 ^ 64 /\
   length bytes = 40%nat)%Z.

Lemma integer_array_address_opt_in : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepIntegerArrayAddress) in idtac.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.IntegerArrayAddress.

Lemma integer_array_address_open_offset
    (args : IntegerAddressArgs) (offset : bv 64) : True.
Proof.
  Fail zesu_integer_pointer_root
    (Z_to_bv 64 (integerAddressBase args) + offset)%bv
    ltac:(fun _ => idtac).
  exact I.
Qed.

Lemma integer_array_address_structural_goal : True.
Proof.
  Fail zesu_integer_array_address_if_enabled.
  exact I.
Qed.

Lemma integer_array_address_projection `{!islaG Sigma} `{!threadG}
    (args : IntegerAddressArgs) (bytes : list (bv 8))
    (Hdomain : integerAddressDomain args bytes) :
  integerAddressBase args ↦ₘ∗ bytes -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (Z_to_bv 64 (integerAddressBase args) + 32)))
    (fun _ => True)%I.
Proof.
  iStartProof.
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
  zesu_integer_array_address_if_enabled.
  let _ := constr:(Hdomain : integerAddressDomain args bytes) in idtac.
  zesu_run.
Qed.
Print Assumptions integer_array_address_projection.

Lemma integer_array_address_nested_offsets `{!islaG Sigma} `{!threadG}
    (args : IntegerAddressArgs) (bytes : list (bv 8))
    (Hdomain : integerAddressDomain args bytes) :
  integerAddressBase args ↦ₘ∗ bytes -∗
  find_in_context
    (FindMemMapsTo
      (bv_unsigned (Z_to_bv 64 (integerAddressBase args) + 24 + 8)))
    (fun _ => True)%I.
Proof.
  iStartProof.
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
  zesu_run.
Qed.
Print Assumptions integer_array_address_nested_offsets.

Lemma integer_array_address_interior `{!islaG Sigma} `{!threadG}
    (base cursor : Z) (bytes : list (bv 8))
    (Hbounds : 0 <= base /\ base <= cursor < base + Z.of_nat (length bytes) /\
      base + Z.of_nat (length bytes) < 2 ^ 64) :
  base ↦ₘ∗ bytes -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (Z_to_bv 64 cursor + 0)))
    (fun _ => True)%I.
Proof.
  iStartProof. iIntros "Hbytes".
  zesu_integer_array_address_if_enabled.
  zesu_run.
Qed.
Print Assumptions integer_array_address_interior.

Lemma integer_array_address_fold_cursor `{!islaG Sigma} `{!threadG}
    (base payloadStart i n : Z) (bytes : list (bv 8))
    (Hbounds : 0 <= base /\ base + Z.of_nat (length bytes) < 2 ^ 64)
    (Hfold : payloadStart = base + 1 /\ 0 <= i < n /\
      payloadStart + n <= base + Z.of_nat (length bytes)) :
  let LET0 := (Z_to_bv 64 (payloadStart + i) + 0)%bv in
  base ↦ₘ∗ bytes -∗
  find_in_context (FindMemMapsTo (bv_unsigned LET0)) (fun _ => True)%I.
Proof.
  intros LET0. iStartProof. iIntros "Hbytes".
  zesu_integer_array_address_if_enabled.
  zesu_run.
Qed.
Print Assumptions integer_array_address_fold_cursor.



Lemma integer_array_address_exclusive_end `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8))
    (Hbounds : 0 <= base /\ base + Z.of_nat (length bytes) < 2 ^ 64) : True.
Proof.
  Fail assert (Hselection : base ↦ₘ∗ bytes ⊢
    find_in_context
      (FindMemMapsTo (bv_unsigned (Z_to_bv 64 (base + Z.of_nat (length bytes)) + 0)))
      (fun _ => True)%I) by
    (iIntros "Hbytes"; zesu_integer_array_address_if_enabled; zesu_run).
  exact I.
Qed.
