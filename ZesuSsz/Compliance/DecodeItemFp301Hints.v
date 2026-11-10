(* Transition hint umbrella of the FP301 decodeItem stack.
   It owns the unfold instances of the caller entry aliases (CallerUnfolds)
   and, later, the registrations of the FP301 meaning module. The October
   umbrella, DecodeItemHints, must not reach this module or Automation2, so
   the October proofs load neither. When the October stack retires, this
   module becomes the decodeItem umbrella.
   `check_decode_item_hints.py` enforces these rules. *)
Require Export ZesuSsz.Generated.DecodeItem.FP301.CallerUnfolds.
