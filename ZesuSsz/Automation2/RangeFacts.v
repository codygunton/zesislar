From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Lia.
From stdpp.bitvector Require Import definitions tactics.
From Ltac2 Require Import Ltac2 Ref List Int String Ident.
Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.SearchBudget.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.
Ltac zesu_range_mentions values pointer T :=
 first [lazymatch T with context[values] => idtac end |
        lazymatch T with context[pointer] => idtac end].
Ltac zesu_range_carrier values pointer root T :=
 first [zesu_range_mentions values pointer T |
        lazymatch T with context[root] => idtac end].
Ltac2 rec zesu_name_prefix source prefix i :=
 if Int.equal i (String.length prefix) then true else
 if Int.ge i (String.length source) then false else
 if Char.equal (String.get source i) (String.get prefix i)
 then zesu_name_prefix source prefix (Int.add i 1) else false.
Ltac zesu_range_pose evidence :=
 let selected := fresh "HrangeFact" in pose proof evidence as selected.
Ltac2 zesu_range_keep evidence :=
 let typ := Constr.type evidence in
 let rec already hyps :=
   match hyps with
   | [] => false
   | h :: rest => let (name, _, previous) := h in
     if zesu_name_prefix (Ident.to_string name) "HrangeFact" 0 then
       if Constr.equal typ previous then true else already rest
     else already rest
   end in
 if already (Control.hyps ()) then () else
 Ltac1.apply (Ltac1.ref [@ZesuSsz; @Automation2; @RangeFacts; @zesu_range_pose])
   [Ltac1.of_constr evidence] Ltac1.run.
(* Project relevant conjuncts without destructing the original assumptions. *)
Ltac zesu_range_project depth values pointer root evidence :=
 let T := type of evidence in
 tryif zesu_range_carrier values pointer root T then
 let leaf := ltac:(tryif zesu_range_mentions values pointer T then
   let keep := ltac2:(e |- zesu_range_keep (Option.get (Ltac1.to_constr e))) in
   keep evidence else idtac) in
 let descend := ltac:(fun remaining left right =>
   let l := constr:(proj1 evidence) in let r := constr:(proj2 evidence) in
   zesu_range_project remaining values pointer root l;
   zesu_range_project remaining values pointer root r) in
 tryif (lazymatch T with ?head _ _ => constr_eq_strict head constr:(and) end)
 then lazymatch T with ?left /\ ?right => descend depth left right end
 else lazymatch T with
 | @eq Z _ _ => leaf | @eq nat _ _ => leaf
 | @eq _ _ _ => idtac
 | Z.le _ _ => leaf | Z.lt _ _ => leaf
 | Z.ge _ _ => leaf | Z.gt _ _ => leaf
 | _ => lazymatch depth with
   | O => idtac
   | S ?remaining =>
     let exposed := eval hnf in T in
     lazymatch exposed with
     | ?left /\ ?right => descend remaining left right
     | _ => idtac end
   end
 end else idtac.
(* Extend selected sum bounds by one layer of summand facts. *)
Ltac zesu_range_project_sum_atom atom evidence :=
 tryif has_evar atom then idtac else
 tryif (let closed := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed atom in idtac)
 then idtac else
 let root := lazymatch atom with ?f ?arg => constr:(arg) | _ => constr:(atom) end in
 zesu_range_project constr:(32%nat) atom atom root evidence.
Ltac2 rec zesu_range_atoms (term : constr) : constr list :=
 lazy_match! term with
 | @eq Z ?lhs ?rhs => List.append (zesu_range_atoms lhs) (zesu_range_atoms rhs)
 | @eq nat ?lhs ?rhs => [lhs; rhs]
 | Z.le ?lhs ?rhs => List.append (zesu_range_atoms lhs) (zesu_range_atoms rhs)
 | Z.lt ?lhs ?rhs => List.append (zesu_range_atoms lhs) (zesu_range_atoms rhs)
 | Z.ge ?lhs ?rhs => List.append (zesu_range_atoms lhs) (zesu_range_atoms rhs)
 | Z.gt ?lhs ?rhs => List.append (zesu_range_atoms lhs) (zesu_range_atoms rhs)
 | Z.add ?lhs ?rhs => List.append (zesu_range_atoms lhs) (zesu_range_atoms rhs)
 | Z.sub ?lhs ?rhs => List.append (zesu_range_atoms lhs) (zesu_range_atoms rhs)
 | Z.mul ?lhs ?rhs => List.append (zesu_range_atoms lhs) (zesu_range_atoms rhs)
 | bv_unsigned (Z_to_bv ?width ?value) => [term; value]
 | _ => [term]
 end.
Ltac2 rec zesu_range_has_atom atom atoms :=
 match atoms with
 | [] => false
 | h :: rest => if Constr.equal atom h then true else zesu_range_has_atom atom rest
 end.
(* Cache syntax once. Opaque data arguments are leaves, not search spaces. *)
Ltac2 rec zesu_range_syntax term :=
 let children :=
   let typ := Constr.type term in
   let arithmetic :=
     if Constr.equal typ constr:(Prop) then true else
     if Constr.equal typ constr:(Z) then true else
     if Constr.equal typ constr:(nat) then true else
     if Constr.equal typ constr:(N) then true else
     if Constr.equal typ constr:(bool) then true else
     lazy_match! typ with | bv _ => true | _ => false end in
   if arithmetic then
     match Constr.Unsafe.kind term with
     | Constr.Unsafe.App _ args =>
       Array.fold_left (fun found arg => List.append found (zesu_range_syntax arg)) [] args
     | Constr.Unsafe.Cast value _ _ => zesu_range_syntax value
     | _ => []
     end
   else [] in
 term :: children.
Ltac2 zesu_range_occurs atom syntax := zesu_range_has_atom atom syntax.
Ltac2 zesu_range_carried selector syntax :=
 let (values, pointer, root) := selector in
 Bool.or (zesu_range_occurs values syntax)
   (Bool.or (zesu_range_occurs pointer syntax) (zesu_range_occurs root syntax)).
Ltac2 zesu_range_selected selector syntax :=
 let (values, pointer, _) := selector in
 Bool.or (zesu_range_occurs values syntax) (zesu_range_occurs pointer syntax).
Ltac2 rec zesu_range_all_paths selector paths :=
 match paths with
 | [] => true
 | syntax :: rest =>
   if zesu_range_carried selector syntax then zesu_range_all_paths selector rest else false
 end.
(* Project a hypothesis once. Never unfold into resource or data arguments. *)
Ltac2 rec zesu_range_leaves depth evidence typ paths :=
 let syntax := zesu_range_syntax typ in
 let paths := syntax :: paths in
 let leaf := fun () => [(evidence, typ, syntax, paths)] in
 let descend := fun remaining lhs rhs =>
   let l := constr:(@proj1 $lhs $rhs $evidence) in
   let r := constr:(@proj2 $lhs $rhs $evidence) in
   List.append (zesu_range_leaves remaining l lhs paths)
     (zesu_range_leaves remaining r rhs paths) in
 (* Structural conjunction descent does not consume predicate-unfold fuel. *)
 let direct := match Constr.Unsafe.kind typ with
   | Constr.Unsafe.App head args =>
     if Constr.equal head constr:(and) then
       Some (Array.get args 0, Array.get args 1) else None
   | _ => None end in
 match direct with
 | Some (lhs, rhs) => descend depth lhs rhs
 | None => lazy_match! typ with
   | @eq Z _ _ => leaf () | @eq nat _ _ => leaf ()
   | @eq _ _ _ => []
   | Z.le _ _ => leaf () | Z.lt _ _ => leaf ()
   | Z.ge _ _ => leaf () | Z.gt _ _ => leaf ()
   | _ =>
     if Int.equal depth 0 then [] else
     if Constr.equal (Constr.type typ) constr:(Prop) then
       let exposed := Std.eval_hnf typ in
       lazy_match! exposed with
       | @and ?lhs ?rhs => descend (Int.sub depth 1) lhs rhs
       | _ => [] end
     else []
   end
 end.
Ltac2 zesu_range_atom_is_open atom :=
 if Constr.has_evar atom then false else
 Control.once (fun () => Control.plus (fun () =>
   Ltac1.apply (Ltac1.ref [@ZesuSsz; @Automation2; @VmClosed; @zesu_vm_closed])
     [Ltac1.of_constr atom] Ltac1.run;
   false) (fun _ => true)).
(* Each hypothesis has one cached projection. Each selected fact is committed once. *)
Ltac2 zesu_range_collect values pointer root :=
 let original := Control.hyps () in
 let cached := List.map (fun h => let (name, _, typ) := h in
   (name, typ, zesu_range_syntax typ, Ref.ref None)) original in
 let chosen := Ref.ref [] in
 List.iter (fun h => let (name, _, typ) := h in
   if zesu_name_prefix (Ident.to_string name) "HrangeFact" 0 then
     Ref.set chosen (typ :: Ref.get chosen) else ()) original;
 let rec any selectors predicate := match selectors with
   | [] => false | h :: rest => if predicate h then true else any rest predicate end in
 let select := fun selectors =>
   List.iter (fun h => let (name, typ, syntax, projection) := h in
     if any selectors (fun selector => zesu_range_carried selector syntax) then (
       let leaves := match Ref.get projection with
         | Some found => found
         | None => let found := zesu_range_leaves 32 (Control.hyp name) typ [] in
           Ref.set projection (Some found); found end in
       List.iter (fun leaf => let (evidence, fact, syntax, paths) := leaf in
         if any selectors (fun selector =>
           Bool.and (zesu_range_selected selector syntax) (zesu_range_all_paths selector paths)) then
           if zesu_range_has_atom fact (Ref.get chosen) then () else (
             Ltac1.apply (Ltac1.ref [@ZesuSsz; @Automation2; @RangeFacts; @zesu_range_pose])
               [Ltac1.of_constr evidence] Ltac1.run;
             Ref.set chosen (fact :: Ref.get chosen))
         else ()) leaves)
     else ()) cached in
 select [(values, pointer, root)];
 let visited := Ref.ref [] in
 let rec close remaining :=
   if Int.equal remaining 0 then () else (
     let selectors := Ref.ref [] in
     let selected := Ref.get chosen in
     List.iter (fun typ => List.iter (fun atom =>
       if zesu_range_has_atom atom (Ref.get visited) then () else (
         Ref.set visited (atom :: Ref.get visited);
         if zesu_range_atom_is_open atom then
           let root := lazy_match! atom with | ?f ?arg => arg | _ => atom end in
           Ref.set selectors ((atom, atom, root) :: Ref.get selectors)
         else ())) (zesu_range_atoms typ)) selected;
     select (Ref.get selectors);
     close (Int.sub remaining 1)) in
 close 2.
Ltac2 rec zesu_range_contains needle term :=
 if Constr.equal needle term then true else
 match Constr.Unsafe.kind term with
 | Constr.Unsafe.App head args =>
   Array.fold_left (fun found arg => if found then true else zesu_range_contains needle arg)
     (zesu_range_contains needle head) args
 | Constr.Unsafe.Cast value _ _ => zesu_range_contains needle value
 | _ => false
 end.
(* An extent proof needs the length equation of each list in its goal. *)
Ltac2 zesu_range_goal_length goal typ :=
 lazy_match! typ with
 | @eq nat (@List.length _ ?values) _ => zesu_range_contains values goal
 | _ => false
 end.
Ltac2 rec zesu_range_erase_list goal hyps :=
 match hyps with
 | [] => []
 | h :: rest =>
   let (name, body, typ) := h in
   let tail := zesu_range_erase_list goal rest in
   if Constr.equal (Constr.type typ) constr:(Prop) then
    if zesu_name_prefix (Ident.to_string name) "HrangeFact" 0
    then tail
    else if zesu_range_goal_length goal typ then tail
    else name :: tail
   else tail
 end.
(* Keep only the selected arithmetic facts in this isolated proof. *)
Ltac2 zesu_range_isolate () :=
 Std.clear (zesu_range_erase_list (Control.goal ()) (Control.hyps ())).
Ltac zesu_selected_closed_bounds :=
 repeat match goal with
 | H : (?lhs < ?rhs)%Z |- _ =>
   let reduced := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed rhs in
   progress change (lhs < reduced)%Z in H
 | H : (?lhs <= ?rhs)%Z |- _ =>
   let reduced := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed rhs in
   progress change (lhs <= reduced)%Z in H
 end.
(* Each rewrite removes a cast. Range proofs use only selected facts. *)
Ltac zesu_selected_casts :=
 repeat match goal with
 | H : context [bv_unsigned (Z_to_bv ?width ?value)] |- _ =>
   assert_fails (has_evar value);
   let bound := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_modulus width) in
   let range := fresh "HrangeFactCast" in
   assert (range : (0 <= value < bv_modulus width)%Z) by (
     change (0 <= value < bound)%Z;
     zesu_selected_closed_bounds;
     Lia.lia);
   progress rewrite (Z_to_bv_small width value range) in H;
   clear range
 end.
Ltac zesu_range_reduce_fact evidence :=
 let normalized := fresh "HrangeFactNormalized" in
 revert evidence;
 ZesuSsz.Automation2.SearchBudget.zesu_normalize_closed_goal;
 intro normalized.
Ltac2 zesu_range_reduce_selected () :=
 let selected := Control.hyps () in
 List.iter (fun h => let (name, _, _) := h in
   if zesu_name_prefix (Ident.to_string name) "HrangeFact" 0 then
     Ltac1.apply (Ltac1.ref [@ZesuSsz; @Automation2; @RangeFacts; @zesu_range_reduce_fact])
       [Ltac1.of_constr (Control.hyp name)] Ltac1.run
   else ()) selected;
 Ltac1.apply (Ltac1.ref [@ZesuSsz; @Automation2; @SearchBudget; @zesu_normalize_closed_goal])
   [] Ltac1.run.
Ltac zesu_selected_array_range :=
 lazymatch goal with
 | |- (?pointer <= ?index < ?upper)%Z =>
   lazymatch upper with context[List.length ?values] =>
     let root := lazymatch values with ?f ?arg => constr:(arg) | _ => constr:(values) end in
     let collect := ltac2:(v p r |- zesu_range_collect
       (Option.get (Ltac1.to_constr v)) (Option.get (Ltac1.to_constr p))
       (Option.get (Ltac1.to_constr r))) in
     (collect values pointer root);
     ltac2:(zesu_range_isolate ());
     (repeat progress (rewrite ?stdpp.list.length_insert, ?stdpp.list.length_app,
        ?stdpp.list.length_take, ?stdpp.list.length_drop;
        cbn [List.length]));
     (repeat match goal with
      | Hlength : List.length ?xs = ?n |- context[List.length ?xs] => progress rewrite Hlength end);
     zesu_selected_casts;
     ltac2:(zesu_range_reduce_selected ());
     lia
   end
 end.


Ltac zesu_word_range base :=
 let root := lazymatch base with ?f ?arg => constr:(arg) | _ => constr:(base) end in
 let collect := ltac2:(v p r |- zesu_range_collect
   (Option.get (Ltac1.to_constr v)) (Option.get (Ltac1.to_constr p))
   (Option.get (Ltac1.to_constr r))) in
 (collect base base root);
 ltac2:(zesu_range_isolate ());
 zesu_selected_casts;
 zesu_selected_closed_bounds;
 lazymatch goal with |- (0 <= ?value < ?bound)%Z =>
   let reduced := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed bound in
   change (0 <= value < reduced)%Z
 end;
 lia.
Lemma zesu_cast_add_no_wrap width base (offset : bv width)
 (Hbase : (0 <= base < bv_modulus width)%Z)
 (Hsum : (0 <= base + bv_unsigned offset < bv_modulus width)%Z) :
 bv_unsigned (bv_add (Z_to_bv width base) offset) = (base + bv_unsigned offset)%Z.
Proof.
 rewrite bv_add_unsigned, (Z_to_bv_small width base Hbase).
 apply bv_wrap_small. exact Hsum.
Qed.
(* Reject symbolic offsets before evaluating their unsigned value. *)
Ltac zesu_address_equality :=
 lazymatch goal with
 | |- bv_unsigned (bv_add (Z_to_bv ?width ?base) ?offset) = ?integer =>
   let displacement := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_unsigned offset) in
   change (bv_unsigned (bv_add (Z_to_bv width base) offset) = base + displacement)%Z;
   let Hbase := fresh "HaddressBaseRange" in
   assert (Hbase : (0 <= base < bv_modulus width)%Z) by zesu_word_range base;
   let Hsum := fresh "HaddressSumRange" in
   assert (Hsum : (0 <= base + displacement < bv_modulus width)%Z) by zesu_word_range base;
   exact (zesu_cast_add_no_wrap width base offset Hbase Hsum)
 end.
