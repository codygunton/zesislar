Require Import ZesuSsz.Automation2.All.
From Coq Require Import ZArith.ZArith Lia.
From Ltac2 Require Import Ltac2 List Int.
Require Import ZesuSsz.Automation2.MemoryAddress.
Require Import ZesuSsz.Automation2.All.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.
Module M.
Lemma closed_stable : True.
Proof.
 ltac2:(if ZesuSsz.Automation2.MemoryAddress.zesu_stack_symbolic_atom constr:((1+2)%Z) then Control.throw (Tactic_failure None) else ()).
 Fail ltac2:(if ZesuSsz.Automation2.MemoryAddress.zesu_stack_symbolic_atom constr:((1+2)%Z) then () else Control.zero (Tactic_failure None)).
 exact I.
Qed.
Lemma symbolic_stable (x:Z) : True.
Proof.
 ltac2:(if ZesuSsz.Automation2.MemoryAddress.zesu_stack_symbolic_atom constr:(x) then () else Control.throw (Tactic_failure None)).
 Fail ltac2:(if ZesuSsz.Automation2.MemoryAddress.zesu_stack_symbolic_atom constr:(x) then Control.zero (Tactic_failure None) else ()).
 exact I.
Qed.
Lemma existing_seed (x y z:Z) (HrangeFactExisting:y<=z) (Hy:0<=y) : x<=x.
Proof.
 ltac2:(ZesuSsz.Automation2.MemoryAddress.zesu_stack_isolate_goal ()).
 assert_succeeds (match goal with H : 0 <= y |- _ => idtac end).
 apply Z.le_refl.
Qed.
Lemma one_layer (x y z:Z) (Hxy:x<=y) (Hyz:y<=z) (Hz:0<=z) : x<=x.
Proof.
 ltac2:(ZesuSsz.Automation2.MemoryAddress.zesu_stack_isolate_goal ()).
 assert_succeeds (match goal with H : y<=z |- _ => idtac end).
 Fail match goal with H : 0<=z |- _ => idtac end.
 apply Z.le_refl.
Qed.
Lemma fixture_fact (x : Z) (n : nat) : x <= x + Z.of_nat n.
Proof. lia. Qed.
Ltac add_facts x count := lazymatch count with
| O => idtac
| S ?remaining => let fact := fresh "Hfixture" in
  pose proof (fixture_fact x count) as fact;
  let literal := eval vm_compute in (Z.of_nat count) in
  change (x <= x + literal) in fact;
  add_facts x remaining
end.

Lemma selection_deduplicates (x y : Z)
 (Hx : 0 <= x) (Hxcopy : 0 <= x) (Hy : 0 <= y) : 0 <= x.
Proof.
 assert_succeeds ltac2:(ZesuSsz.Automation2.MemoryAddress.zesu_stack_isolate_goal ()).
 ltac2:(ZesuSsz.Automation2.MemoryAddress.zesu_stack_isolate_goal ()).
 ltac2:(let selected := List.filter (fun h => let (name, _, _) := h in
   ZesuSsz.Automation2.RangeFacts.zesu_name_prefix (Ident.to_string name) "HrangeFact" 0)
   (Control.hyps ()) in
   if Int.equal (List.length selected) 1 then ()
   else Control.throw (Tactic_failure None)).
 assumption.
Qed.


Lemma boundary (x : Z) : x <= x.
Proof.
 idtac "FIXTURE_BEGIN".
 add_facts x constr:(512%nat).
 idtac "FIXTURE_END".
 assert_succeeds ltac2:(
 ZesuSsz.Automation2.MemoryAddress.zesu_stack_isolate_goal ();
 let selected := List.filter (fun h => let (name, _, _) := h in
   ZesuSsz.Automation2.RangeFacts.zesu_name_prefix (Ident.to_string name) "HrangeFact" 0) (Control.hyps ()) in
 if Int.equal (List.length selected) 512 then Message.print (Message.of_string "EXACTLY_512_DISTINCT_SELECTED")
 else Control.throw (Tactic_failure None)).
 idtac "AT_LIMIT_SELECTION_PASSED".
 pose proof (fixture_fact x 513) as Hover.
 change (x <= x + 513) in Hover.
 Fail ltac2:(ZesuSsz.Automation2.MemoryAddress.zesu_stack_isolate_goal ()).
 idtac "OVER_LIMIT_REFUSAL_PASSED".
 assert_succeeds (let T := type of Hover in idtac).
 apply Z.le_refl.
Qed.

End M.
Definition expected_closed : True := M.closed_stable.
Definition expected_symbolic : forall x:Z, True := M.symbolic_stable.
Definition expected_seed : forall x y z:Z, y<=z -> 0<=y -> x<=x := M.existing_seed.
Definition expected_layer : forall x y z:Z, x<=y -> y<=z -> 0<=z -> x<=x := M.one_layer.
Print Assumptions M.closed_stable.
Print Assumptions M.symbolic_stable.
Print Assumptions M.existing_seed.
Print Assumptions M.one_layer.

Definition expected_limit : forall x:Z, x<=x := M.boundary.
Print Assumptions M.boundary.
Print Assumptions M.selection_deduplicates.
