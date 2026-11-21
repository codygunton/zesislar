From Coq Require Import ZArith.ZArith Lists.List.
From stdpp Require Import base list bitvector.definitions.
Local Open Scope Z_scope.

(* The classes the call-site step of `CallSlice.v` reads.

   A callee that takes an input slice and an output slot registers its
   interface once: how its argument record is built, the size of its output
   slot, the words of its outcome that name the payload and the consumed count,
   and the four interface lemmas the step applies. A caller registers the
   lemma that proves the callee's domain from the caller's own domain. The step
   names neither: it finds both by instance search on the predicates in the
   goal and in the context. *)

Class ZesuCallSliceInterface {A O : Type}
    (domain : A -> Prop) (meaning : A -> O -> Prop) := {
  (* argument words, stack pointer, input end, input bytes, output bytes *)
  zesu_call_slice_args :
    list (bv 64) -> bv 64 -> Z -> list (bv 8) -> list (bv 8) -> A;
  zesu_call_slice_out_size : nat;
  zesu_call_slice_payload_pointer : O -> bv 64;
  (* the same word, in the 8-byte load form a block computes *)
  zesu_call_slice_payload_pointer_load : O -> bv 64;
  zesu_call_slice_payload_length : O -> bv 64;
  zesu_call_slice_consumed : O -> bv 64;
  (* a payload length below this bound lies inside the input *)
  zesu_call_slice_payload_limit : Z;
  zesu_call_slice_domain_input :
    forall argv0 argv1 argv2 rest sp inputEnd input before,
      domain (zesu_call_slice_args (argv0 :: argv1 :: argv2 :: rest) sp inputEnd input before) ->
      bv_unsigned argv2 = Z.of_nat (length input) /\
      bv_unsigned argv1 + bv_unsigned argv2 < bv_modulus 64;
  zesu_call_slice_consumed_le :
    forall argv sp inputEnd input before after,
      meaning (zesu_call_slice_args argv sp inputEnd input before) after ->
      bv_unsigned (zesu_call_slice_consumed after) <= Z.of_nat (length input);
  zesu_call_slice_payload_in_input :
    forall argv0 argv1 rest sp inputEnd input before after,
      meaning (zesu_call_slice_args (argv0 :: argv1 :: rest) sp inputEnd input before) after ->
      0 < bv_unsigned (zesu_call_slice_payload_length after) ->
      bv_unsigned (zesu_call_slice_payload_length after) < zesu_call_slice_payload_limit ->
      bv_unsigned argv1 <= bv_unsigned (zesu_call_slice_payload_pointer after) /\
      bv_unsigned (zesu_call_slice_payload_pointer after) +
        bv_unsigned (zesu_call_slice_payload_length after) <=
        bv_unsigned argv1 + Z.of_nat (length input);
  zesu_call_slice_payload_in_input_load :
    forall argv0 argv1 rest sp inputEnd input before after,
      meaning (zesu_call_slice_args (argv0 :: argv1 :: rest) sp inputEnd input before) after ->
      0 < bv_unsigned (zesu_call_slice_payload_length after) ->
      bv_unsigned (zesu_call_slice_payload_length after) < zesu_call_slice_payload_limit ->
      bv_unsigned argv1 <= bv_unsigned (zesu_call_slice_payload_pointer_load after) /\
      bv_unsigned (zesu_call_slice_payload_pointer_load after) +
        bv_unsigned (zesu_call_slice_payload_length after) <=
        bv_unsigned argv1 + Z.of_nat (length input)
}.
Global Hint Mode ZesuCallSliceInterface - - ! - : typeclass_instances.

(* The caller side: a call on any window [p, p + l) of the caller's input,
   with the callee's stack pointer at `frame args` and its output slot at
   `frame args + k`, `0 <= k <= slotLimit`, satisfies the callee's domain.
   The data the step needs to state the premises are the class indices. *)
Class ZesuCallSliceCaller {Args A O : Type} (callerDomain : Args -> Prop)
    {domain : A -> Prop} {meaning : A -> O -> Prop}
    (I : ZesuCallSliceInterface domain meaning)
    (inputBase : Args -> Z) (inputBytes : Args -> list (bv 8))
    (frame : Args -> Z) (inputEnd : Args -> Z) (slotLimit : Z) :=
  zesu_call_slice_caller_domain :
    forall args (p l out sp : bv 64) (k ie : Z) (rest : list (bv 64)) (before : list (bv 8)),
      callerDomain args ->
      inputBase args <= bv_unsigned p /\
      bv_unsigned p + bv_unsigned l <= inputBase args + Z.of_nat (length (inputBytes args)) ->
      bv_unsigned sp = frame args ->
      bv_unsigned out = frame args + k -> 0 <= k <= slotLimit ->
      ie = inputEnd args ->
      length before = @zesu_call_slice_out_size _ _ _ _ I ->
      domain (@zesu_call_slice_args _ _ _ _ I (out :: p :: l :: rest) sp ie
        (take (Z.to_nat (bv_unsigned l))
          (drop (Z.to_nat (bv_unsigned p - inputBase args)) (inputBytes args)))
        before).
Global Hint Mode ZesuCallSliceCaller - - - ! - - - - - - - - : typeclass_instances.

(* A caller whose contract bounds the payload length a call on its whole
   input returns: below the interface's limit, so the payload lies inside
   that input (`zesu_call_slice_payload_in_input_load`). *)
Class ZesuCallSliceCallerPayloadBound {Args A O : Type} (callerDomain : Args -> Prop)
    {domain : A -> Prop} {meaning : A -> O -> Prop}
    (I : ZesuCallSliceInterface domain meaning) (inputBytes : Args -> list (bv 8)) :=
  zesu_call_slice_caller_payload_bound :
    forall args argv sp ie before after,
      callerDomain args ->
      meaning (@zesu_call_slice_args _ _ _ _ I argv sp ie (inputBytes args) before) after ->
      bv_unsigned (@zesu_call_slice_payload_length _ _ _ _ I after) <
        @zesu_call_slice_payload_limit _ _ _ _ I.
Global Hint Mode ZesuCallSliceCallerPayloadBound - - - ! - - ! - : typeclass_instances.

(* A caller whose contract places the window of a call itself (the slice is
   the caller's own input): `window args` states it. *)
Class ZesuCallSliceCallerWindow {Args : Type} (callerDomain : Args -> Prop)
    (window : Args -> Prop) :=
  zesu_call_slice_caller_window : forall args, callerDomain args -> window args.
Global Hint Mode ZesuCallSliceCallerWindow - ! - : typeclass_instances.

(* A callee that takes its input slice by reference: its first argument is
   the output slot, its second the address of two words the caller stored,
   the slice's pointer and its length. `mk` builds the callee's argument
   record from the argument words, the stack pointer, the slice pointer, the
   input end and the slice bytes. A call on any window [p, p + l) of the
   caller's input, with the callee's stack pointer at `frame args`, the output
   slot at `frame args + k` and the two words at `frame args + j`, both within
   `slotLimit` and `slotSize` apart, satisfies the callee's domain. *)
Class ZesuCallSliceRefCaller {Args A : Type} (callerDomain : Args -> Prop)
    (domain : A -> Prop)
    (mk : list (bv 64) -> bv 64 -> bv 64 -> bv 64 -> list (bv 8) -> A)
    (inputBase : Args -> Z) (inputBytes : Args -> list (bv 8))
    (frame : Args -> Z) (inputEnd : Args -> bv 64) (slotLimit slotSize : Z) :=
  zesu_call_slice_ref_caller_domain :
    forall args (out ref p l sp : bv 64) (k j : Z) (rest : list (bv 64)),
      callerDomain args ->
      inputBase args <= bv_unsigned p /\
      bv_unsigned p + bv_unsigned l <= inputBase args + Z.of_nat (length (inputBytes args)) ->
      bv_unsigned sp = frame args ->
      bv_unsigned out = frame args + k -> 0 <= k <= slotLimit ->
      bv_unsigned ref = frame args + j -> 0 <= j <= slotLimit ->
      (k + slotSize <= j \/ j + slotSize <= k) ->
      domain (mk (out :: ref :: rest) sp p (inputEnd args)
        (take (Z.to_nat (bv_unsigned l))
          (drop (Z.to_nat (bv_unsigned p - inputBase args)) (inputBytes args)))).
Global Hint Mode ZesuCallSliceRefCaller - - ! ! - - - - - - - : typeclass_instances.

(* What a by-reference callee hands back about the slice it consumed: its
   result record `result c r` places the rest it returns (`restPointer r`,
   `restLength r`) at the end of the slice the call record `c` names
   ([inputPointer c, inputPointer c + length (input c))). The class reads
   the slice through the record's projections, so the step finds it whether
   the context holds the record as the constructor application the entry
   states or as the record value a simplification left. The call step reads
   the window of a later call's slice from it when that slice is the rest
   the callee returned. *)
Class ZesuCallSliceRefResult {C R : Type} (result : C -> R -> Prop)
    (inputPointer : C -> Z) (input : C -> list (bv 8)) (restPointer restLength : R -> Z) :=
  zesu_call_slice_ref_result_window :
    forall c r,
      result c r ->
      inputPointer c <= restPointer r /\
      restPointer r + restLength r = inputPointer c + Z.of_nat (length (input c)) /\
      0 <= restLength r /\ restPointer r + restLength r < bv_modulus 64.
Global Hint Mode ZesuCallSliceRefResult - - ! - - - - : typeclass_instances.
