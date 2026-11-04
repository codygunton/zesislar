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

Definition byte_image_splice (before field : list (bv 8)) (offset : nat) :=
  take offset before ++ field ++ drop (offset + length field) before.

Lemma byte_image_closed_codec :
  bv_to_little_endian 8 8 (bv_unsigned (BV 64 0)) =
    List.repeat (BV 8 0) 8.
Proof. zesu_byte_class_image. Qed.

Lemma byte_image_complete_words (before : list (bv 8))
    (Hlength : length before = 40%nat) :
  byte_image_splice
    (byte_image_splice
      (byte_image_splice
        (byte_image_splice
          (byte_image_splice before
            (bv_to_little_endian 8 8 (bv_unsigned (BV 64 4))) 32)
          (bv_to_little_endian 8 8 (bv_unsigned (BV 64 0))) 0)
        (bv_to_little_endian 8 8 (bv_unsigned (BV 64 0))) 8)
      (bv_to_little_endian 8 8 (bv_unsigned (BV 64 0))) 16)
    (bv_to_little_endian 8 8 (bv_unsigned (BV 64 0))) 24 =
  List.repeat (BV 8 0) 32 ++ [BV 8 4] ++ List.repeat (BV 8 0) 7.
Proof. unfold byte_image_splice. zesu_byte_class_image. Qed.

Lemma byte_image_symbolic_offset (offset : nat) (before : list (bv 8)) : True.
Proof.
  Fail assert (Himage : take offset before = []) by zesu_byte_class_image.
  exact I.
Qed.

Lemma byte_image_symbolic_codec (word : bv 64) : True.
Proof.
  Fail assert (Himage : bv_to_little_endian 8 8 (bv_unsigned word) =
    List.repeat (BV 8 0) 8) by zesu_byte_class_image.
  exact I.
Qed.

Lemma byte_image_changed_source (left right : list (bv 8)) : True.
Proof. Fail assert (Himage : left = right) by zesu_byte_class_image. exact I. Qed.

Lemma byte_image_wrong_closed_value : True.
Proof.
  Fail assert (Himage : [BV 8 0] = [BV 8 1]) by zesu_byte_class_image.
  exact I.
Qed.

Lemma byte_image_symbolic_width (width : N) (word : bv width) : True.
Proof.
  Fail assert (Himage : bv_to_little_endian 8 width (bv_unsigned word) = [])
    by zesu_byte_class_image.
  exact I.
Qed.
