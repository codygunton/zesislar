Class ZesuCallSet : Prop := zesu_call_set : True.

Ltac zesu_call_set_on :=
  let _ := constr:(_ : ZesuCallSet) in idtac.
