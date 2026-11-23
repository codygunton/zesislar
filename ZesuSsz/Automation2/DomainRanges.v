From Coq Require Import ZArith.

(* Domain ranges as plain facts.

   A function domain is one folded predicate in a block's context. The
   solvers (`bv_solve`, `zesu_lia`, the linear normal form) and the context
   filters never open it, so a pointer range stated inside it is invisible to
   them. A contract registers the ranges of its domain once, as a
   `ZesuDomainRanges domain ranges` instance; `zesu_pose_domain_ranges` poses
   them, split into their conjuncts, when the domain fact enters the context.
   The domain stays folded. *)

Class ZesuDomainRanges (domain ranges : Prop) : Prop :=
  zesu_domain_ranges : domain -> ranges.

(* The lookup is indexed by the domain: a hypothesis whose head has no
   instance fails at once. *)
Global Hint Mode ZesuDomainRanges ! - : typeclass_instances.

(* Succeeds when every conjunct of `ranges` is already a hypothesis. *)
Ltac zesu_domain_ranges_present ranges :=
  lazymatch ranges with
  | ?left /\ ?right =>
      zesu_domain_ranges_present left; zesu_domain_ranges_present right
  | _ => match goal with _ : ranges |- _ => idtac end
  end.

(* A conjunct `Z.of_nat (length l) = N` with a numeral N up to 4096 also
   gives `length l = N` in `nat`: the list-length rewrites and the array
   lookup's bounds read lengths in that form only (an owned 24-byte result
   record whose contract states its length in `Z`). A `nat` numeral is unary,
   hence the bound. *)
Ltac zesu_domain_ranges_split H :=
  lazymatch type of H with
  | _ /\ _ =>
      let left := fresh "Hrange" in
      let right := fresh "Hrange" in
      destruct H as [left right];
      zesu_domain_ranges_split left; zesu_domain_ranges_split right
  | Z.of_nat (@length ?T ?l) = ?n =>
      tryif (lazymatch n with Zpos _ => idtac | Z0 => idtac end;
             let small := eval vm_compute in (Z.leb n 4096) in
             constr_eq small true)
      then (let m := eval vm_compute in (Z.to_nat n) in
            let Hlength := fresh "Hlength" in
            assert (Hlength : @length T l = m) by
              exact (Nat2Z.inj _ _ (H : Z.of_nat (@length T l) = Z.of_nat m)))
      else idtac
  | _ => idtac
  end.

(* For each hypothesis `H : domain` with an instance whose ranges are not all
   in the context yet: pose them once, split. Idempotent. *)
Ltac zesu_pose_domain_ranges :=
  repeat match goal with
  | H : ?domain |- _ =>
      lazymatch type of domain with Prop => idtac end;
      let ranges_proof := constr:(zesu_domain_ranges (domain:=domain) H) in
      let ranges := type of ranges_proof in
      tryif zesu_domain_ranges_present ranges then fail else idtac;
      let R := fresh "Hrange" in
      pose proof ranges_proof as R;
      zesu_domain_ranges_split R
  end.

(* Succeeds when the goal's premise is a domain with registered ranges. One
   instance lookup: the gate that keeps `zesu_pose_domain_ranges` (a scan of
   the whole context) off the many implications that bring no domain. *)
Ltac zesu_domain_ranges_premise :=
  lazymatch goal with
  | |- ?premise -> _ =>
      lazymatch type of premise with Prop => idtac end;
      let _ := constr:(fun H : premise => zesu_domain_ranges (domain:=premise) H) in
      idtac
  end.