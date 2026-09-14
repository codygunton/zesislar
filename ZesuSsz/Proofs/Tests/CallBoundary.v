Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Calls.

Lemma call_boundary_roundtrip `{!islaG Sigma} `{!threadG}
    (stack_size : Z)
    (P : list (bv 64) -> bv 64 ->
      ((list (bv 64) -> iProp Sigma) -> iProp Sigma) -> iProp Sigma) :
  zesu_call stack_size P -∗ zesu_call stack_size P.
Proof.
  iStartProof. iIntros "Hspec". zesu_unpack_call "Hspec".
  subst r10 r11 r12 r13 r14 r15 r16 r17.
  iExists sp, ret. zesu_run.
Qed.
Print Assumptions call_boundary_roundtrip.

Lemma call_boundary_mask (value : bv 64) :
  Z.land (bv_unsigned value) 131072 = 0 ->
  bv_and value (BV 64 131072) = BV 64 0.
Proof. intros Hmask. zesu_finish. Qed.
Print Assumptions call_boundary_mask.

Lemma call_boundary_constant :
  (Z_to_bv 64 65868 + BV 64 604020736 +
    BV 64 18446744073709551468)%bv = BV 64 604086456.
Proof. zesu_finish. Qed.
Print Assumptions call_boundary_constant.

Lemma call_boundary_identity `{!islaG Sigma} `{!threadG}
    (value : bv 64) (P : bv 64 -> iProp Sigma) :
  P (bv_sign_extend 64 value) -∗ P value.
Proof. iStartProof. iIntros "HP". zesu_run. Qed.
Print Assumptions call_boundary_identity.

Lemma call_boundary_zero `{!islaG Sigma}
    (value : bv 64) (P : bv 64 -> iProp Sigma) (Q : iProp Sigma) :
  (P value ∗ Q)%I = (P (value + BV 64 0)%bv ∗ Q)%I.
Proof. zesu_finish. Qed.
Print Assumptions call_boundary_zero.

Lemma call_boundary_optional_end (pointer : bv 64) :
  bv_extract 0 3 pointer = BV 3 0 ->
  bv_unsigned pointer + 8 < (machineRamEnd defaultMap) ->
  bv_unsigned pointer + 9 < (machineRamEnd defaultMap).
Proof. intros Halign Hupper. zesu_finish. Qed.
Print Assumptions call_boundary_optional_end.

Lemma call_boundary_ram_lower (pointer : bv 64) :
  (mapRamBase defaultMap) <= bv_unsigned pointer ->
  bv_unsigned pointer >= bv_unsigned (BV 64 (mapRamBase defaultMap)).
Proof. intros Hlower. zesu_finish. Qed.
Print Assumptions call_boundary_ram_lower.

Lemma call_boundary_ram_add (pointer : bv 64) :
  (mapRamBase defaultMap) <= bv_unsigned pointer ->
  bv_unsigned pointer + 24 < (machineRamEnd defaultMap) ->
  bv_unsigned (pointer + BV 64 8)%bv >= (mapRamBase defaultMap) /\
  bv_unsigned (pointer + BV 64 24)%bv < (machineRamEnd defaultMap).
Proof. intros Hlower Hupper. split; zesu_finish. Qed.
Print Assumptions call_boundary_ram_add.

Lemma call_boundary_stack_alignment (pointer : bv 64) :
  bv_unsigned pointer `mod` 16 = 0 ->
  bv_extract 0 3 pointer = BV 3 0.
Proof. intros Halign. zesu_finish. Qed.
Print Assumptions call_boundary_stack_alignment.

Lemma call_boundary_ram_upper_aligned (pointer : bv 64) :
  bv_extract 0 3 pointer = BV 3 0 ->
  bv_unsigned pointer < (machineRamEnd defaultMap) ->
  bv_unsigned pointer < bv_unsigned (BV 64 (mapRamBase defaultMap) + BV 64 (mapRamSize defaultMap))%bv.
Proof. intros Halign Hupper. zesu_finish. Qed.
Print Assumptions call_boundary_ram_upper_aligned.
