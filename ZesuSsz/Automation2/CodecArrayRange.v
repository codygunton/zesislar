Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.MemoryAddress.
From Coq Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import bitvector.definitions.
Local Open Scope Z_scope.

Class ZesuStepCodecArrayRange : Prop := {}.

(* Length does not depend on the symbolic payload. Only closed counts and
   widths enter this presentation rule. Unsupported codecs must remain refused. *)
Ltac zesu_codec_range_lengths :=
  lazymatch goal with
  | |- context [length (bv_to_little_endian _ _ _)] => idtac
  end;
  repeat match goal with
  | |- context [length (bv_to_little_endian ?count ?width ?value)] =>
      is_closed_term count; is_closed_term width;
      let nonnegative := fresh "HcodecCount" in
      assert (nonnegative : (0 <= count)%Z) by lia;
      rewrite (length_bv_to_little_endian count width value nonnegative);
      clear nonnegative
  end;
  lazymatch goal with
  | |- context [length (bv_to_little_endian _ _ _)] => fail 1
  | _ => idtac
  end.

(* The existing closed-term adapter computes only closed integer terms.
   It preserves symbolic bases. No resource or entry assumption is changed. *)
Ltac zesu_codec_array_range :=
  zesu_switch_enabled constr:(ZesuStepCodecArrayRange);
  solve [
    zesu_codec_range_lengths;
    lazymatch goal with
    | |- (?lower <= ?pointer < ?upper)%Z =>
        ZesuSsz.Automation2.MemoryAddress.zesu_handoff_closed_Z lower ltac:(fun low =>
        ZesuSsz.Automation2.MemoryAddress.zesu_handoff_closed_Z pointer ltac:(fun point =>
        ZesuSsz.Automation2.MemoryAddress.zesu_handoff_closed_Z upper ltac:(fun high =>
          change (low <= point < high)%Z;
          lia)))
    end
  ].
