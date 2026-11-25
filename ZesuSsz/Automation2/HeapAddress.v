(* A memory access whose address equals a place of an owned region only by
   facts: the address is the sum of registers, and each register has an
   equation `bv_unsigned x = t` in the context, while the region's start is
   stated over the terms `t` (an array list's spare region at
   `pointer + length * 40`, stored to through `x11 + (x16 + x12)` with
   `bv_unsigned x11 = pointer`, `bv_unsigned x12 = 8 * length`,
   `bv_unsigned x16 = 32 * length`). The membership gate
   (UninitRegions.zesu_mem_lookup_gate) reads the two sides with different
   roots and refuses such a region, so the access found no resource.

   The reading below replaces each register of the address by its equation
   (a register without one stays its own unsigned value; a cast `Z_to_bv z`
   reads as `z`; shifts and products by literals scale) and asks the linear
   normal form of BvLinear whether the reading minus the region start is a
   constant k. Everything is syntactic: a region without such a constant, or
   one that the membership classifier already relates to the address, is
   refused without a solver. The address is then rewritten to `start + k`;
   the proof needs the region's own range (an owned region lies below 2^64)
   and `k` inside the region, which is the one solver call, on selected
   facts. *)
From Coq Require Import List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.BvLinear.
Require ZesuSsz.Automation2.VmClosed.
From Ltac2 Require Import Ltac2 Constr Std.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

Lemma zesu_heap_address_offset (pointer : bv 64) (lower k c count : Z) :
  pointer = Z_to_bv 64 (lower + (k - c)) ->
  0 <= lower -> lower + count <= 2 ^ 64 -> 0 <= c <= k -> k < count ->
  bv_unsigned pointer + c = lower + k.
Proof.
  intros -> Hlow Hhigh Hc Hk.
  rewrite Z_to_bv_small; [lia|]. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.

Lemma zesu_heap_address_base (pointer : bv 64) (lower k count : Z) :
  pointer = Z_to_bv 64 (lower + (k - 0)) ->
  0 <= lower -> lower + count <= 2 ^ 64 -> 0 <= k -> k < count ->
  bv_unsigned pointer = lower + k.
Proof.
  intros Hp Hlow Hhigh Hk Hcount.
  rewrite <- (Z.add_0_r (bv_unsigned pointer)).
  exact (zesu_heap_address_offset pointer lower k 0 count Hp Hlow Hhigh (conj (Z.le_refl 0) Hk) Hcount).
Qed.

Lemma zesu_heap_register_cast (x : bv 64) (t : Z) :
  bv_unsigned x = t -> x = Z_to_bv 64 t.
Proof. intros <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* The equations `bv_unsigned x = t` of the context, x of width 64. *)
Ltac2 zesu_heap_facts () : (constr * constr * ident) list :=
  List.flat_map (fun (name, body, typ) =>
    match body with
    | Some _ => []
    | None =>
        lazy_match! typ with
        | @eq Z (@bv_unsigned ?width ?x) ?t =>
            if Constr.equal width constr:(64%N) then
              if Constr.has_evar typ then [] else [(x, t, name)]
            else []
        | _ => []
        end
    end) (Control.hyps ()).

Ltac2 zesu_heap_fact (facts : (constr * constr * ident) list) (x : constr) :=
  List.find_opt (fun (y, _, _) => Constr.equal x y) facts.

Ltac2 zesu_heap_closed_value (term : constr) : constr :=
  Std.eval_vm None constr:(bv_unsigned $term).

(* The integer reading of a 64-bit term, equal to its unsigned value modulo
   2^64. `used` collects the registers read through an equation. *)
Ltac2 rec zesu_heap_read (facts : (constr * constr * ident) list)
    (used : (constr * ident) list ref) (term : constr) : constr :=
  let read := zesu_heap_read facts used in
  lazy_match! term with
  | bv_add ?a ?b => let a := read a in let b := read b in constr:(Z.add $a $b)
  | bv_sub ?a ?b => let a := read a in let b := read b in constr:(Z.sub $a $b)
  | bv_shiftl ?a ?s =>
      if zesu_bvlin_closed s then
        let a := read a in
        let factor := Std.eval_vm None constr:(2 ^ bv_unsigned $s) in
        constr:(Z.mul $a $factor)
      else constr:(@bv_unsigned 64 $term)
  | bv_mul ?a ?b =>
      if zesu_bvlin_closed b then
        let a := read a in let b := zesu_heap_closed_value b in constr:(Z.mul $a $b)
      else if zesu_bvlin_closed a then
        let b := read b in let a := zesu_heap_closed_value a in constr:(Z.mul $a $b)
      else constr:(@bv_unsigned 64 $term)
  | Z_to_bv _ ?z => z
  | _ =>
      if zesu_bvlin_closed term then zesu_heap_closed_value term else
      match zesu_heap_fact facts term with
      | Some (_, t, name) =>
          (if List.exist (fun (y, _) => Constr.equal y term) (Ref.get used) then ()
           else Ref.set used ((term, name) :: Ref.get used));
          t
      | None => constr:(@bv_unsigned 64 $term)
      end
  end.

(* `Some k` when value - lower is the constant k in the linear normal form. *)
Ltac2 zesu_heap_constant_difference (value : constr) (lower : constr) : constr option :=
  let state := { bv_atoms := []; bv_literals := []; z_atoms := [] } in
  match Control.case (fun () =>
    zesu_bvlin_reify_z constr:(64%N) state constr:(Z.sub $value $lower)) with
  | Val (syntax, _) =>
      let result := Std.eval_vm None constr:(match zesuZNorm $syntax with
        | Some (constant, terms) =>
            if forallb (fun entry => Z.eqb (snd entry) 0) terms then Some constant else None
        | None => None end) in
      lazy_match! result with
      | Some ?k => Some k
      | _ => None
      end
  | Err _ => None
  end.

(* The address `bv_unsigned pointer` or `bv_unsigned pointer + c`, c a
   numeral: (pointer, c). *)
Ltac2 zesu_heap_address_parts (address : constr) : (constr * constr) option :=
  lazy_match! address with
  | Z.add (@bv_unsigned ?width ?pointer) ?c =>
      if Constr.equal width constr:(64%N) then
        if zesu_mem_numeral c then Some (pointer, c) else None
      else None
  | @bv_unsigned ?width ?pointer =>
      if Constr.equal width constr:(64%N) then Some (pointer, constr:(0%Z)) else None
  | _ => None
  end.

(* The offset k of the address in the region at `lower` of `size` bytes,
   read through the context's register equations; it fails when the region
   start and the address differ by no constant, when the constant lies
   before the region or before the address's own offset, or when the
   membership classifier already relates the address to the region (its
   rules handle that region). Runs `found k` on success. *)
Ltac2 zesu_heap_region_offset (address : constr) (lower : constr) (size : constr)
    (found : Ltac1.t) :=
  match zesu_heap_address_parts address with
  | None => Control.zero (Tactic_failure None)
  | Some (pointer, c) =>
      (match zesu_mem_range_verdict lower address size with
       | ZesuMemPossible => Control.zero (Tactic_failure None)
       | _ => ()
       end);
      let used := Ref.ref [] in
      let value := zesu_heap_read (zesu_heap_facts ()) used pointer in
      match zesu_heap_constant_difference constr:(Z.add $value $c) lower with
      | Some k =>
          if Constr.equal (Std.eval_vm None constr:(andb (Z.leb 0 $c) (Z.leb $c $k))) constr:(true) then
            Ltac1.apply found [Ltac1.of_constr k] Ltac1.run
          else Control.zero (Tactic_failure None)
      | None => Control.zero (Tactic_failure None)
      end
  end.

Ltac zesu_heap_region_offset address lower size found :=
  let run := ltac2:(address lower size found |-
    zesu_heap_region_offset (Option.get (Ltac1.to_constr address))
      (Option.get (Ltac1.to_constr lower)) (Option.get (Ltac1.to_constr size)) found) in
  run address lower size found.

Ltac zesu_heap_cast_register x name :=
  let Hcast := fresh "HheapRegister" in
  pose proof (zesu_heap_register_cast x _ name) as Hcast;
  rewrite Hcast; clear Hcast.

(* Proves `pointer = Z_to_bv 64 v`: each register read through an equation
   becomes the cast of its value, then the linear normal form decides. *)
Ltac2 zesu_heap_pointer_cast () :=
  lazy_match! goal with
  | [ |- @eq (bv _) ?pointer _ ] =>
      let used := Ref.ref [] in
      let _ := zesu_heap_read (zesu_heap_facts ()) used pointer in
      List.iter (fun (x, name) =>
        Ltac1.apply (Ltac1.ref [@ZesuSsz; @Automation2; @HeapAddress; @zesu_heap_cast_register])
          [Ltac1.of_constr x; Ltac1.of_ident name] Ltac1.run) (Ref.get used);
      ltac1:(ZesuSsz.Automation2.BvLinear.zesu_bv_linear_bv)
  end.

Ltac zesu_heap_pointer_cast := ltac2:(zesu_heap_pointer_cast ()).

(* `address = lower + k` from the region range `Hrange` (0 <= lower and
   lower + count <= 2^64) and `Hinside` (k < count). *)
Ltac zesu_heap_address_equation address lower k count Hlow Hhigh Hinside :=
  lazymatch address with
  | (bv_unsigned ?pointer + ?c)%Z =>
      refine (zesu_heap_address_offset pointer lower k c count _ Hlow Hhigh _ Hinside);
      [zesu_heap_pointer_cast | split; apply Z.leb_le; reflexivity]
  | bv_unsigned ?pointer =>
      refine (zesu_heap_address_base pointer lower k count _ Hlow Hhigh _ Hinside);
      [zesu_heap_pointer_cast | apply Z.leb_le; reflexivity]
  end.
