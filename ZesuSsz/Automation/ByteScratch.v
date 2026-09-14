Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ByteArrays.

(* Singleton arrays also match the upstream word rule by conversion.
   Match the byte-array prefix first, so the rule retains its scratch tail. *)
Global Existing Instance subsume_mem_scratch_byte_array_1_uninit_inst | 0.
