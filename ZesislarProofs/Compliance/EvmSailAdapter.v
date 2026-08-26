From Coq Require Import Lists.List ZArith.ZArith.
Require Import EvmSail.evm_decoder_types.

Import ListNotations.

(** An evaluator gives meaning to the prompt monad and its host operations.
    A later proof must supply and validate one concrete evaluator. *)
Record DecoderEvaluator : Type := {
  evaluates : forall A, M A -> list Z -> option A -> Prop
}.

(** The generated action remains a field because Coq 8 cannot compile its
    large well-founded recursion in practical time.  A Rocq 9 build can set
    this field to [EvmSail.evm_decoder.decode_stateless_input]. *)
Record DecoderModel : Type := {
  decodeAction : StatelessInputRef -> M StatelessInput
}.

Definition ReferenceDecodes
    (runner : DecoderEvaluator)
    (model : DecoderModel)
    (bytes : list Z)
    (inputRef : StatelessInputRef)
  (decoded : StatelessInput) : Prop :=
  evaluates runner StatelessInput (decodeAction model inputRef) bytes (Some decoded).

Definition ReferenceRejects
    (runner : DecoderEvaluator)
    (model : DecoderModel)
    (bytes : list Z)
    (inputRef : StatelessInputRef) : Prop :=
  evaluates runner StatelessInput (decodeAction model inputRef) bytes None.
