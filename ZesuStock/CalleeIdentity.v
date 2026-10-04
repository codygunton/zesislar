From Coq Require Import ZArith.ZArith.

(** A call names a direct entry or a slot in the selected vtable. *)
Inductive CalleeId : Type :=
| CalleeEntry (entry : Z)
| CalleeVtableSlot (slot : Z).
