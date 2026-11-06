Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.CodecRoundtrip.
Require Import ZesuSsz.Automation2.ArrayContinuation.
Require Import ZesuSsz.Automation2.SymbolicByteCodec.

Class ZesuStepCodecFrame : Prop := {}.

#[export] Instance codec_frame_roundtrip `{ZesuStepCodecFrame} :
  ZesuStepCodecRoundtrip := {}.
#[export] Instance codec_frame_array `{ZesuStepCodecFrame} :
  ZesuStepArrayContinuation := {}.
#[export] Instance codec_frame_bytes `{ZesuStepCodecFrame} :
  ZesuStepSymbolicByteCodec := {}.

(* The spatial branch checks the exact owner, width, fraction and payload.
   The pure branch proves only the mathematical codec identity. *)
Ltac zesu_codec_frame :=
  zesu_switch_enabled constr:(ZesuStepCodecFrame);
  first [solve [zesu_codec_roundtrip] |
    zesu_array_continuation ltac:(zesu_symbolic_byte_codec)].
