Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ByteClassGuards.
From Coq Require Import List Bool.Bool ZArith.ZArith.
From stdpp Require Import bitvector.definitions decidable list.
Import ListNotations.
Open Scope Z_scope.

Lemma byte_class_lower :
  129 <= bv_unsigned (BV 8 129) <= 183 /\
  bv_unsigned (bv_and (bv_and (bv_sign_extend 64 (BV 8 129)) (BV 64 255)) (BV 64 127)) = bv_unsigned (BV 8 129) - 128 /\
  1 + (bv_unsigned (BV 8 129) - 128) <= bv_unsigned (BV 64 2).
Proof.
  assert (Hnegative : bool_decide (bv_signed (bv_sign_extend 128 (bv_sign_extend 64 (BV 8 129))) < bv_signed (BV 128 0)) = true) by (vm_compute; reflexivity).
  assert (Hnot128 : negb (bool_decide (bv_and (bv_sign_extend 64 (BV 8 129)) (BV 64 255) = BV 64 128)) = true) by (vm_compute; reflexivity).
  assert (Hupper : negb (bool_decide (bv_signed (BV 128 183) < bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 (BV 8 129)) (BV 64 255))))) = true) by (vm_compute; reflexivity).
  assert (Hlength : negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_and (bv_sign_extend 64 (BV 8 129)) (BV 64 255)) (BV 64 127))) >= bv_signed (bv_zero_extend 128 (BV 64 2)))) = true) by (vm_compute; reflexivity).
  zesu_byte_class_guards.
  exact HbyteClassFacts.
Qed.

Lemma byte_class_alternate_upper :
  129 <= bv_unsigned (BV 8 190) <= 191 /\
  bv_unsigned (bv_and (bv_and (bv_sign_extend 64 (BV 8 190)) (BV 64 255)) (BV 64 127)) = bv_unsigned (BV 8 190) - 128 /\
  1 + (bv_unsigned (BV 8 190) - 128) <= bv_unsigned (BV 64 63).
Proof.
  assert (Hnegative : bool_decide (bv_signed (bv_sign_extend 128 (bv_sign_extend 64 (BV 8 190))) < bv_signed (BV 128 0)) = true) by (vm_compute; reflexivity).
  assert (Hnot128 : negb (bool_decide (bv_and (bv_sign_extend 64 (BV 8 190)) (BV 64 255) = BV 64 128)) = true) by (vm_compute; reflexivity).
  assert (Hupper : negb (bool_decide (bv_signed (BV 128 191) < bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 (BV 8 190)) (BV 64 255))))) = true) by (vm_compute; reflexivity).
  assert (Hlength : negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_and (bv_sign_extend 64 (BV 8 190)) (BV 64 255)) (BV 64 127))) >= bv_signed (bv_zero_extend 128 (BV 64 63)))) = true) by (vm_compute; reflexivity).
  zesu_byte_class_guards.
  exact HbyteClassFacts.
Qed.

Lemma byte_class_missing_guard (byte : bv 8) : True.
Proof. Fail zesu_byte_class_guards. exact I. Qed.

Lemma byte_class_symbolic_upper (byte : bv 8) (lengthWord : bv 64) (upperWord : bv 128)
  (Hnegative : bool_decide (bv_signed (bv_sign_extend 128 (bv_sign_extend 64 byte)) < bv_signed (BV 128 0)) = true)
  (Hnot128 : negb (bool_decide (bv_and (bv_sign_extend 64 byte) (BV 64 255) = BV 64 128)) = true)
  (Hupper : negb (bool_decide (bv_signed upperWord < bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (BV 64 255))))) = true)
  (Hlength : negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 127))) >= bv_signed (bv_zero_extend 128 lengthWord))) = true) : True.
Proof. Fail zesu_byte_class_guards. exact I. Qed.

Lemma byte_class_nonbyte (word : bv 16) (lengthWord : bv 64)
  (Hnegative : bool_decide (bv_signed (bv_sign_extend 128 (bv_sign_extend 64 word)) < bv_signed (BV 128 0)) = true)
  (Hnot128 : negb (bool_decide (bv_and (bv_sign_extend 64 word) (BV 64 255) = BV 64 128)) = true)
  (Hupper : negb (bool_decide (bv_signed (BV 128 183) < bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 word) (BV 64 255))))) = true)
  (Hlength : negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_and (bv_sign_extend 64 word) (BV 64 255)) (BV 64 127))) >= bv_signed (bv_zero_extend 128 lengthWord))) = true) : True.
Proof. Fail zesu_byte_class_guards. exact I. Qed.

Lemma byte_image_prefix (before suffix : list (bv 8)) (prefix start count : nat)
  (Hwindow : (start + count <= prefix)%nat) (Hprefix : (prefix <= length before)%nat) :
  take count (drop start (take prefix before ++ suffix)) = take count (drop start before).
Proof. zesu_byte_class_image. Qed.

Lemma byte_image_wrong_goal (value : Z) : value = value.
Proof. Fail zesu_byte_class_image. reflexivity. Qed.

Lemma byte_class_wrong_payload (byte : bv 8) (lengthWord : bv 64)
  (Hnegative : bool_decide (bv_signed (bv_sign_extend 128 (bv_sign_extend 64 byte)) < bv_signed (BV 128 0)) = true)
  (Hnot128 : negb (bool_decide (bv_and (bv_sign_extend 64 byte) (BV 64 255) = BV 64 128)) = true)
  (Hupper : negb (bool_decide (bv_signed (BV 128 183) < bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 byte) (BV 64 255))))) = true)
  (Hlength : negb (bool_decide (bv_signed (bv_zero_extend 128 (BV 64 0)) >= bv_signed (bv_zero_extend 128 lengthWord))) = true) : True.
Proof. Fail zesu_byte_class_guards. exact I. Qed.
