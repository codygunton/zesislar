From Coq Require Import ZArith.ZArith Lists.List NArith.NArith Lia.
From stdpp Require Import base list bitvector.definitions.
From iris.proofmode Require Import environments tactics.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.NamedEquation.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation2.CallSliceInterface.
Require Import ZesuSsz.Automation2.DomainRanges.
Require Import ZesuSsz.Automation2.InteriorByteSlice.
Require ZesuSsz.Automation2.ResourceGroups.
Require ZesuSsz.Automation2.BytePositionEquations.
Require ZesuSsz.Automation2.WrappedWord.
Require ZesuSsz.Automation2.PureFacts.
Require ZesuSsz.Automation2.ByteExtractCodec281.
Require ZesuSsz.Automation2.VmClosed.
Local Open Scope Z_scope.

(* The call-site step for a callee that takes an input slice and an output
   slot (`CallSliceInterface.v`).

   At the existential the callee's call spec asks for,
     ∃ x, bv_unsigned p ↦ₘ∗ x.2 ∗ bv_unsigned out ↦ₘ∗ x.1 ∗
          ⌜domain (args (_ :: _ :: l :: _) sp _ x.2 x.1)⌝ ∗ …,
   the step finds the window [p, p + l) inside a held byte array, lends it with
   both byte lists as explicit witnesses, takes the output slot from a held
   array or carves it out of an uninitialised region, proves the callee's
   domain once from the caller's lemma and keeps it, and states the callee's
   stack pointer over the caller's root word. `zesu_call_restore` puts a
   returned slice back into the array it was lent from, whatever the goal. *)

(* Library `lia`, not the project override: every call below runs in a
   cleared context. *)
Ltac zesu_call_slice_lia := Coq.micromega.Zify.zify; xlia Coq.micromega.Lia.zchecker.

Lemma zesu_call_slice_add_exact (a b : bv 64) :
  bv_unsigned a + bv_unsigned b < 18446744073709551616 ->
  bv_unsigned (bv_add a b) = bv_unsigned a + bv_unsigned b.
Proof.
  intros Hlt. rewrite bv_add_unsigned. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ a) as Ha. pose proof (bv_unsigned_in_range _ b) as Hb.
  change (bv_modulus 64) with 18446744073709551616 in *. zesu_call_slice_lia.
Qed.

Lemma zesu_call_slice_sub_exact (a b : bv 64) :
  bv_unsigned b <= bv_unsigned a ->
  bv_unsigned (bv_sub a b) = bv_unsigned a - bv_unsigned b.
Proof.
  intros Hle. rewrite bv_sub_unsigned. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ a) as Ha. pose proof (bv_unsigned_in_range _ b) as Hb.
  change (bv_modulus 64) with 18446744073709551616 in *. zesu_call_slice_lia.
Qed.

(* A window [p, p+l) inside [base, base+len), advanced by a consumed count
   c <= l. *)
Lemma zesu_call_slice_window_advance (base len : Z) (p l c : bv 64) :
  bv_unsigned p + bv_unsigned l < bv_modulus 64 ->
  (base <= bv_unsigned p /\ bv_unsigned p + bv_unsigned l <= base + len) ->
  bv_unsigned c <= bv_unsigned l ->
  bv_unsigned (bv_add p c) = bv_unsigned p + bv_unsigned c /\
  bv_unsigned (bv_sub l c) = bv_unsigned l - bv_unsigned c /\
  (base <= bv_unsigned (bv_add p c) /\
   bv_unsigned (bv_add p c) + bv_unsigned (bv_sub l c) <= base + len).
Proof.
  intros Hfit [Hlo Hhi] Hc. change (bv_modulus 64) with 18446744073709551616 in *.
  pose proof (bv_unsigned_in_range _ c) as Hcr. pose proof (bv_unsigned_in_range _ l) as Hlr.
  rewrite zesu_call_slice_add_exact; [|zesu_call_slice_lia].
  rewrite zesu_call_slice_sub_exact; [|zesu_call_slice_lia]. zesu_call_slice_lia.
Qed.

(* An address word that is a closed-offset chain of a root word, as an
   integer. *)
Ltac zesu_call_slice_word_address_solve :=
  rewrite ?bv_add_unsigned ?bv_sub_unsigned ?Z_to_bv_unsigned; unfold bv_wrap;
  change (bv_modulus 64) with 18446744073709551616 in *;
  repeat match goal with
  | |- context [bv_unsigned (@BV ?n ?z ?wf)] => change (bv_unsigned (@BV n z wf)) with z
  end;
  Z.to_euclidean_division_equations; zesu_call_slice_lia.

(* The consumed count of the last call on a window is at most the window
   length. *)
Lemma zesu_call_slice_take_length_le {A} (n : Z) (k : nat) (l : list A) (c : Z) :
  c <= Z.of_nat (length (take (Z.to_nat n) (drop k l))) -> 0 <= n -> c <= n.
Proof. rewrite length_take. intros. zesu_call_slice_lia. Qed.

(* The length of a window [p, p + l) taken out of an array at `base`. *)
Lemma zesu_call_slice_window_length {A} (base p l : Z) (bytes : list A) :
  base <= p /\ p + l <= base + Z.of_nat (length bytes) -> 0 <= l ->
  Z.of_nat (length (take (Z.to_nat l) (drop (Z.to_nat (p - base)) bytes))) = l.
Proof. intros [? ?] ?. rewrite length_take length_drop. zesu_call_slice_lia. Qed.

(* A whole array as the window [p, p + length) of itself: offset 0, full
   length. *)
Lemma zesu_call_slice_take_drop_whole {A} (b l : Z) (bytes : list A) :
  Z.of_nat (length bytes) = l ->
  take (Z.to_nat l) (drop (Z.to_nat (b - b)) bytes) = bytes.
Proof.
  intros <-. rewrite Z.sub_diag Nat2Z.id. cbn [Z.to_nat].
  rewrite drop_0. apply take_ge. zesu_call_slice_lia.
Qed.

(* The rest a by-reference call returned (`ZesuCallSliceRefResult`) lies in
   the window its slice was taken from. *)
Lemma zesu_call_slice_rest_window {A} (base : Z) (bytes : list A) (p0 l0 pw lw : bv 64)
    (rp rl : Z) :
  base <= bv_unsigned p0 /\ bv_unsigned p0 + bv_unsigned l0 <= base + Z.of_nat (length bytes) ->
  bv_unsigned p0 <= rp /\
  rp + rl = bv_unsigned p0 + Z.of_nat (length (take (Z.to_nat (bv_unsigned l0))
                                                (drop (Z.to_nat (bv_unsigned p0 - base)) bytes))) /\
  0 <= rl /\ rp + rl < bv_modulus 64 ->
  pw = Z_to_bv 64 rp -> lw = Z_to_bv 64 rl ->
  base <= bv_unsigned pw /\ bv_unsigned pw + bv_unsigned lw <= base + Z.of_nat (length bytes).
Proof.
  intros [Hlo Hhi] (Hp & Hsum & Hl & Hmax) -> ->.
  pose proof (bv_unsigned_in_range _ p0) as Hp0.
  pose proof (bv_unsigned_in_range _ l0) as Hl0.
  rewrite length_take length_drop in Hsum.
  rewrite !Z_to_bv_small; zesu_call_slice_lia.
Qed.

(* The rest record of `ZesuCallSliceRefResult` read for a slice (p0, input)
   the record names through its projections. *)
Lemma zesu_call_slice_ref_result_at {C R : Type} {result : C -> R -> Prop}
    {ip : C -> Z} {inp : C -> list (bv 8)} {rp rl : R -> Z}
    (I : ZesuCallSliceRefResult result ip inp rp rl) (c : C) (r : R) (p0 : bv 64)
    (input : list (bv 8)) :
  result c r -> ip c = bv_unsigned p0 -> inp c = input ->
  bv_unsigned p0 <= rp r /\ rp r + rl r = bv_unsigned p0 + Z.of_nat (length input) /\
  0 <= rl r /\ rp r + rl r < bv_modulus 64.
Proof.
  intros Hres Hp Hi. rewrite <- Hp, <- Hi. exact (zesu_call_slice_ref_result_window c r Hres).
Qed.

Lemma zesu_call_slice_unsigned_pos n (w : bv n) : bv_unsigned w <> 0 -> 0 < bv_unsigned w.
Proof. pose proof (bv_unsigned_in_range n w). zesu_call_slice_lia. Qed.

(* The payload a call returned lies inside that call's input once a later
   call's domain was established on it. *)
Lemma zesu_call_slice_payload_window {A O : Type} {domain : A -> Prop}
    {meaning : A -> O -> Prop} (I : ZesuCallSliceInterface domain meaning)
    (argv0 ipw : bv 64) rest sp ie (bytes before : list (bv 8)) (after : O)
    (o2 p l : bv 64) rest2 sp2 ie2 before2 :
  meaning (@zesu_call_slice_args _ _ _ _ I (argv0 :: ipw :: rest) sp ie bytes before) after ->
  zesu_named_eq p (@zesu_call_slice_payload_pointer _ _ _ _ I after) ->
  zesu_named_eq l (@zesu_call_slice_payload_length _ _ _ _ I after) ->
  bv_unsigned (@zesu_call_slice_payload_length _ _ _ _ I after) <> 0 ->
  domain (@zesu_call_slice_args _ _ _ _ I (o2 :: p :: l :: rest2) sp2 ie2
    (take (Z.to_nat (bv_unsigned l)) (drop (Z.to_nat (bv_unsigned p - bv_unsigned ipw)) bytes))
    before2) ->
  Z.of_nat (length bytes) < @zesu_call_slice_payload_limit _ _ _ _ I ->
  bv_unsigned ipw <= bv_unsigned p /\
  bv_unsigned p + bv_unsigned l <= bv_unsigned ipw + Z.of_nat (length bytes).
Proof.
  intros Hmean [Hp] [Hl] Hnz Hdom Hsmall. subst p l.
  pose proof (proj1 (@zesu_call_slice_domain_input _ _ _ _ I _ _ _ _ _ _ _ _ Hdom)) as Hlen.
  rewrite length_take length_drop in Hlen.
  apply (@zesu_call_slice_payload_in_input _ _ _ _ I _ _ _ _ _ _ _ _ Hmean).
  - apply zesu_call_slice_unsigned_pos; exact Hnz.
  - zesu_call_slice_lia.
Qed.

(* `size` bytes of an uninitialised region at distance `d`, as an array of
   unknown bytes. *)
Lemma zesu_call_slice_uninit_carve `{!islaG Sigma} (a d n size : Z) (count : nat) :
  size = Z.of_nat count -> 0 <= d -> d + size <= n ->
  a ↦ₘ? n -∗
  a ↦ₘ? d ∗ (∃ values : list (bv 8), ⌜length values = count⌝ ∗ (a + d) ↦ₘ∗ values) ∗
  (a + d + size) ↦ₘ? (n - d - size).
Proof.
  iIntros (Hsize Hd Hn) "H".
  iDestruct (mem_mapsto_uninit_split d with "H") as "[$ H]"; [zesu_call_slice_lia|].
  iDestruct (mem_mapsto_uninit_split size with "H") as "[H $]"; [zesu_call_slice_lia|].
  iDestruct (ZesuSsz.Contracts.IslarisMemory.mem_mapsto_uninit_to_byte_array with "H")
    as (values Hlen) "H".
  iExists values. iFrame. iPureIntro. zesu_call_slice_lia.
Qed.

Lemma zesu_call_slice_uninit_carve0 `{!islaG Sigma} (a n size : Z) (count : nat) :
  size = Z.of_nat count -> size <= n ->
  a ↦ₘ? n -∗
  (∃ values : list (bv 8), ⌜length values = count⌝ ∗ a ↦ₘ∗ values) ∗ (a + size) ↦ₘ? (n - size).
Proof.
  iIntros (Hsize Hn) "H".
  iDestruct (mem_mapsto_uninit_split size with "H") as "[H $]"; [zesu_call_slice_lia|].
  iDestruct (ZesuSsz.Contracts.IslarisMemory.mem_mapsto_uninit_to_byte_array with "H")
    as (values Hlen) "H".
  iExists values. iFrame. iPureIntro. zesu_call_slice_lia.
Qed.

(* A stack-pointer equation the restore rewrites the goal with. *)
Definition zesu_call_slice_addr_fact (P : Prop) : Prop := P.

(* The word an address term is a closed-offset chain of. *)
Ltac zesu_call_slice_root t :=
  lazymatch t with
  | @bv_unsigned _ ?w => zesu_call_slice_root w
  | Z_to_bv _ ?z => zesu_call_slice_root z
  | Z.add ?l _ => zesu_call_slice_root l
  | Z.sub ?l _ => zesu_call_slice_root l
  | @bv_add _ ?l _ => zesu_call_slice_root l
  | @bv_sub _ ?l _ => zesu_call_slice_root l
  | _ => constr:(t)
  end.
Ltac zesu_call_slice_root_z root :=
  lazymatch type of root with
  | Z => constr:(root)
  | _ => constr:(bv_unsigned root)
  end.
(* The closed value of an expression over a root word, read off at a sample
   root value (2^62: no offset chain below 2^62 wraps). The value is only a
   candidate; every use proves it. *)
Ltac zesu_call_slice_eval_at root e :=
  let f := eval pattern root in e in
  lazymatch f with
  | ?g _ =>
      lazymatch type of root with
      | Z => let d := eval vm_compute in (g (2 ^ 62)%Z) in d
      | _ => let d := eval vm_compute in (g (Z_to_bv 64 (2 ^ 62))) in d
      end
  end.

(* Close `tac`'s goal in a context cleared to the range facts of a domain
   hypothesis (`DomainRanges.v`), bare or kept under
   `PureFacts.zesu_kept_domain`. *)
Ltac zesu_call_slice_with_ranges tac :=
  match goal with
  | Hd : ZesuSsz.Automation2.PureFacts.zesu_kept_domain ?D |- _ =>
      let Hr := fresh "HcsRanges" in
      pose proof (zesu_domain_ranges (domain:=D)
        (ZesuSsz.Automation2.PureFacts.zesu_kept_domain_elim Hd)) as Hr;
      clear - Hr; tac
  | Hd : ?D |- _ =>
      let Hr := fresh "HcsRanges" in
      pose proof (zesu_domain_ranges (domain:=D) Hd) as Hr;
      clear - Hr; tac
  end.

Ltac zesu_call_slice_address := zesu_call_slice_with_ranges zesu_call_slice_word_address_solve.

(* Derive the window of a call's slice that is the payload the previous call
   returned, for entries that state no window fact. *)
Ltac zesu_call_slice_payload_windows I dom meaning mk :=
  let limit := eval vm_compute in (@zesu_call_slice_payload_limit _ _ _ _ I) in
  repeat match goal with
  | Hdom : dom (mk (_ :: ?p :: ?l :: _) _ _ _ _),
    Hp : zesu_named_eq ?p _,
    Hl : zesu_named_eq ?l ?wl,
    Hnz : bv_unsigned ?wl <> 0%Z,
    Hmean : meaning (mk (_ :: ?ipw :: _) _ _ ?bytes _) _ |- _ =>
      lazymatch goal with
      | _ : (bv_unsigned ipw <= bv_unsigned p)%Z |- _ => fail
      | _ => idtac
      end;
      let Hw := fresh "HcsPayloadWindow" in
      let Hsmall := fresh "HcsSmall" in
      assert (Hsmall : (Z.of_nat (length bytes) < limit)%Z)
        by (zesu_call_slice_with_ranges zesu_call_slice_lia);
      pose proof (zesu_call_slice_payload_window I _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hmean Hp Hl Hnz Hdom Hsmall) as Hw;
      clear Hsmall;
      destruct Hw as [? ?]
  end.

(* `bv_wrap n z = z` for every wrapped integer of the goal whose range the
   context decides. *)
Ltac zesu_call_slice_wrap_small :=
  repeat match goal with
  | |- context [bv_wrap ?n ?z] =>
      let m := eval vm_compute in (2 ^ Z.of_N n)%Z in
      let E := fresh "HcsWrap" in
      assert (E : bv_wrap n z = z)
        by (apply bv_wrap_small; unfold bv_modulus;
            change (2 ^ Z.of_N n)%Z with m; zesu_call_slice_lia);
      rewrite E; clear E
  end.

(* (p, l) is the rest a by-reference call returned (its record `result c r`
   with a `ZesuCallSliceRefResult` instance, `p = Z_to_bv 64 (restPointer r)`,
   `l = Z_to_bv 64 (restLength r)`) on a slice (p0, l0) of the array at [base]
   with [bytes] (`inputPointer c = bv_unsigned p0`, `input c` the window of
   (p0, l0), both by conversion, so `c` may be the constructor application or
   the record value): [win p0 l0 k0] finds the window of the slice, [k]
   receives the window of (p, l). *)
Ltac zesu_call_slice_rest_window_step p l base bytes win k :=
  match goal with
  | Hres : context [take (Z.to_nat (bv_unsigned ?l0))
                      (drop (Z.to_nat (bv_unsigned ?p0 - base)) bytes)] |- _ =>
      lazymatch type of Hres with
      | ?res ?c ?r =>
      let C := constr:(_ : ZesuCallSliceRefResult res _ _ _ _) in
      let ip := lazymatch type of C with @ZesuCallSliceRefResult _ _ _ ?ip _ _ _ => ip end in
      let inp := lazymatch type of C with @ZesuCallSliceRefResult _ _ _ _ ?inp _ _ => inp end in
      let rp := lazymatch type of C with @ZesuCallSliceRefResult _ _ _ _ _ ?rp _ => rp end in
      let rl := lazymatch type of C with @ZesuCallSliceRefResult _ _ _ _ _ _ ?rl => rl end in
      let input := constr:(take (Z.to_nat (bv_unsigned l0))
                             (drop (Z.to_nat (bv_unsigned p0 - base)) bytes)) in
      let Hip := fresh "HcsRestFrom" in
      assert (Hip : ip c = bv_unsigned p0) by reflexivity;
      let Hin := fresh "HcsRestInput" in
      assert (Hin : inp c = input) by reflexivity;
      let Hpw := fresh "HcsRestP" in
      assert (Hpw : p = Z_to_bv 64 (rp r)) by first [assumption | reflexivity];
      let Hlw := fresh "HcsRestL" in
      assert (Hlw : l = Z_to_bv 64 (rl r)) by first [assumption | reflexivity];
      win p0 l0 ltac:(fun Hw0 =>
        k constr:(zesu_call_slice_rest_window base bytes p0 l0 p l (rp r) (rl r) Hw0
                    (zesu_call_slice_ref_result_at C c r p0 input Hres Hip Hin)
                    Hpw Hlw))
      end
  end.

(* The window [p, p+l) of the array at [base] with [bytes]: passes to [k] a
   proof of base <= bv_unsigned p /\ bv_unsigned p + bv_unsigned l <=
   base + length bytes. *)
Ltac zesu_call_slice_window I dom meaning mk p l base bytes k :=
  let limit := eval vm_compute in (@zesu_call_slice_payload_limit _ _ _ _ I) in
  first
  [ (* the entry states the window of (p, l) *)
    match goal with
    | Hlo : (base <= bv_unsigned p)%Z,
      Hhi : (bv_unsigned p + bv_unsigned l <= base + Z.of_nat (length bytes))%Z |- _ =>
        k constr:(conj Hlo Hhi)
    end
  | (* (p, l) = (p0 + c, l0 - c): the last call consumed c of the stated
       window (p0, l0) *)
    lazymatch p with
    | bv_add ?p0 ?c =>
      lazymatch l with
      | bv_sub ?l0 c =>
        match goal with
        | Hlo : (base <= bv_unsigned p0)%Z,
          Hhi : (bv_unsigned p0 + bv_unsigned l0 <= base + Z.of_nat (length bytes))%Z,
          Hdom : dom (mk (_ :: p0 :: l0 :: _) _ _ _ _),
          Hmean : meaning (mk (_ :: p0 :: l0 :: _) _ _ _ _) _ |- _ =>
            let Hfit := fresh "HcsFit" in
            pose proof (proj2 (@zesu_call_slice_domain_input _ _ _ _ I _ _ _ _ _ _ _ _ Hdom))
              as Hfit;
            let Hc0 := fresh "HcsConsumed0" in
            pose proof (zesu_call_slice_take_length_le _ _ _ _
              (@zesu_call_slice_consumed_le _ _ _ _ I _ _ _ _ _ _ Hmean)
              (proj1 (bv_unsigned_in_range _ l0))) as Hc0;
            let Hc := fresh "HcsConsumed" in
            first
            [ pose proof (Hc0 : (bv_unsigned c <= bv_unsigned l0)%Z) as Hc
            | (* the count was loaded in this block: its 8-byte load form
                 reads as the byte positions the interface states *)
              lazymatch c with
              | Z_to_bv ?width (little_endian_to_bv 8 (take ?count (drop ?start ?loaded))) =>
                  ZesuSsz.Automation2.BytePositionEquations.zesu_le_window_equation
                    width count start loaded
                    ltac:(fun Hwindow =>
                      assert (Hc : (bv_unsigned c <= bv_unsigned l0)%Z)
                        by (rewrite Hwindow; exact Hc0))
              end ];
            let Hadv := fresh "HcsAdvance" in
            pose proof (zesu_call_slice_window_advance _ _ p0 l0 c Hfit (conj Hlo Hhi) Hc) as Hadv;
            k constr:(proj2 (proj2 Hadv))
        end
      end
    end
  | (* (p, l) is the payload the previous call returned, its pointer in the
       8-byte load form: the interface places it inside that call's input
       when its length is positive and below the interface's bound *)
    lazymatch base with
    | bv_unsigned ?ipw =>
      match goal with
      | Hmean : meaning (mk (_ :: ipw :: _) _ _ bytes _) _ |- _ =>
        match goal with
        | Hnz : bv_unsigned l <> 0%Z |- _ =>
            let Hlt := fresh "HcsNoWrap" in
            first
            [ match goal with
              | H : (bv_unsigned l < limit)%Z |- _ => pose proof H as Hlt
              end
            | assert (Hlt : (bv_unsigned l < limit)%Z) by (eauto 3)
            | (* the caller's contract bounds the payload of a call on its
                 whole input (`ZesuCallSliceCallerPayloadBound`) *)
              match goal with
              | Hcd : ?cd0 ?args0 |- _ =>
                  let fact := lazymatch cd0 with
                    | ZesuSsz.Automation2.PureFacts.zesu_kept_domain => args0
                    | _ => constr:(cd0 args0) end in
                  let Hwf := lazymatch cd0 with
                    | ZesuSsz.Automation2.PureFacts.zesu_kept_domain =>
                        constr:(ZesuSsz.Automation2.PureFacts.zesu_kept_domain_elim Hcd)
                    | _ => constr:(Hcd) end in
                  lazymatch fact with
                  | ?cd ?args =>
                      let C := constr:(_ : ZesuCallSliceCallerPayloadBound cd I _) in
                      pose proof (@zesu_call_slice_caller_payload_bound _ _ _ cd _ _ I _ C
                        args _ _ _ _ _ Hwf Hmean : (bv_unsigned l < limit)%Z) as Hlt
                  end
              end ];
            k constr:((@zesu_call_slice_payload_in_input_load _ _ _ _ I _ _ _ _ _ _ _ _ Hmean
                         (zesu_call_slice_unsigned_pos _ l Hnz) Hlt) :
                       (base <= bv_unsigned p /\
                        bv_unsigned p + bv_unsigned l <= base + Z.of_nat (length bytes))%Z)
        end
      end
    end
  | (* (p, l) is the rest a by-reference call returned on a slice
       (p0, l0) of the same array *)
    zesu_call_slice_rest_window_step p l base bytes
      ltac:(fun p0 l0 k0 => zesu_call_slice_window I dom meaning mk p0 l0 base bytes k0) k
  | (* the caller's contract places (p, l) *)
    let Hw := fresh "HcsContractWindow" in
    assert (Hw : (base <= bv_unsigned p /\
                  bv_unsigned p + bv_unsigned l <= base + Z.of_nat (length bytes))%Z)
      by (match goal with
          | Hd : ?D ?args |- _ =>
              let Hcw := fresh "HcsCallerWindow" in
              pose proof (zesu_call_slice_caller_window (callerDomain:=D) args Hd) as Hcw;
              cbv beta in Hcw; rewrite ?Z.add_simpl_l in Hcw;
              first [ exact Hcw
                    | cbn [Z.to_nat N.to_nat drop take app List.map List.seq] in Hcw; exact Hcw ]
          end);
    k constr:(Hw)
  | (* (p, l) are integer words `Z_to_bv _ zp`, `Z_to_bv _ zl` (a pointer and
       a length the caller stored and reloaded, read back as words by
       `WrappedWord.zesu_word_explicit_list_rewrite`): the window is linear
       arithmetic over the range facts of the context *)
    lazymatch p with Z_to_bv _ _ => idtac end;
    lazymatch l with Z_to_bv _ _ => idtac end;
    let Hw := fresh "HcsIntegerWindow" in
    assert (Hw : (base <= bv_unsigned p /\
                  bv_unsigned p + bv_unsigned l <= base + Z.of_nat (length bytes))%Z)
      by (rewrite !Z_to_bv_unsigned; zesu_call_slice_wrap_small; zesu_call_slice_lia);
    k constr:(Hw) ].

(* The window of (p, l) for a callee with no by-value interface in reach: the
   window steps of a by-value callee whose call record the context holds, or
   a stated window, or the rest a by-reference call returned. *)
Ltac zesu_call_slice_window_any p l base bytes k :=
  first
  [ once (match goal with
      | Hd : ?ddom (?dmk (_ :: _ :: _ :: _) _ _ _ _) |- _ =>
          let I := constr:(_ : ZesuCallSliceInterface ddom _) in
          let dmeaning := lazymatch type of I with
            | @ZesuCallSliceInterface _ _ _ ?m => m end in
          zesu_call_slice_window I ddom dmeaning dmk p l base bytes k
      end)
  | zesu_call_slice_window_bare p l base bytes k ]
with zesu_call_slice_window_bare p l base bytes k :=
  first
  [ match goal with
    | Hlo : (base <= bv_unsigned p)%Z,
      Hhi : (bv_unsigned p + bv_unsigned l <= base + Z.of_nat (length bytes))%Z |- _ =>
        k constr:(conj Hlo Hhi)
    end
  | zesu_call_slice_rest_window_step p l base bytes
      ltac:(fun p0 l0 k0 => zesu_call_slice_window_any p0 l0 base bytes k0) k ].

(* The callee's output slot: an array the caller holds at that address, or
   `size` bytes carved out of an uninitialised region that contains it.
   Leaves "HcsOutArray" : oa ↦ₘ∗ before, a fact bv_unsigned out = oa, and
   (for a carved slot) length before = count. *)
Ltac zesu_call_slice_out_slot out size count k :=
  let rout := zesu_call_slice_root out in
  first
  [ iMatchHyp ltac:(fun Hout resource2 =>
      lazymatch resource2 with
      | (?oa ↦ₘ∗ ?before)%I =>
          let roa := zesu_call_slice_root oa in
          constr_eq rout roa;
          let d := zesu_call_slice_eval_at rout constr:((bv_unsigned out - oa)%Z) in
          lazymatch d with 0%Z => idtac end;
          let Houta := fresh "HcsOut" in
          assert (Houta : bv_unsigned out = oa) by zesu_call_slice_address;
          iRename Hout into "HcsOutArray";
          k oa before Houta
      end)
  | iMatchHyp ltac:(fun Hu resource2 =>
      lazymatch resource2 with
      | (?ua ↦ₘ? ?n0)%I =>
          let rua := zesu_call_slice_root ua in
          constr_eq rout rua;
          let d := zesu_call_slice_eval_at rout constr:((bv_unsigned out - ua)%Z) in
          let n := zesu_call_slice_eval_at rout n0 in
          let fits := eval vm_compute in ((0 <=? d)%Z && (d + size <=? n)%Z) in
          lazymatch fits with true => idtac end;
          let r := eval vm_compute in (n - d - size)%Z in
          iRename Hu into "HcsU";
          tryif constr_eq n0 n then idtac
          else (let Hn := fresh "HcsSize" in
                assert (Hn : n0 = n) by zesu_call_slice_address;
                iEval (rewrite Hn) in "HcsU"; clear Hn);
          let oa := lazymatch d with 0%Z => constr:(ua) | _ => constr:((ua + d)%Z) end in
          let Houta := fresh "HcsOut" in
          assert (Houta : bv_unsigned out = oa) by zesu_call_slice_address;
          let before := fresh "csBefore" in
          let Hlen := fresh "HcsBeforeLen" in
          lazymatch d with
          | 0%Z =>
              iDestruct (zesu_call_slice_uninit_carve0 ua n size count with "HcsU")
                as "(HcsEx & ?)"; [reflexivity|clear; zesu_call_slice_lia|]
          | _ =>
              iDestruct (zesu_call_slice_uninit_carve ua d n size count with "HcsU")
                as "(? & HcsEx & ?)";
              [reflexivity|clear; zesu_call_slice_lia|clear; zesu_call_slice_lia|]
          end;
          iDestruct "HcsEx" as (before) "[HcsLenP HcsOutArray]";
          iDestruct "HcsLenP" as %Hlen;
          lazymatch d with
          | 0%Z => change (n - size)%Z with r
          | _ => change (n - d - size)%Z with r
          end;
          k oa before Houta
      end) ].

(* The callee's domain, from the caller's lemma (`ZesuCallSliceCaller`). The
   address side goals are closed in a context cleared to the caller's range
   facts. *)
Ltac zesu_call_slice_domain I Hwin Houta oa :=
  lazymatch goal with
  | |- ?dom (?mk (?out :: ?p :: ?l :: _) ?sp _ _ _) =>
    match goal with
    | Hwf0 : ?cd0 ?args0 |- _ =>
      let Hwf_fact := lazymatch cd0 with
        | ZesuSsz.Automation2.PureFacts.zesu_kept_domain => args0
        | _ => constr:(cd0 args0) end in
      let Hwf := lazymatch cd0 with
        | ZesuSsz.Automation2.PureFacts.zesu_kept_domain =>
            constr:(ZesuSsz.Automation2.PureFacts.zesu_kept_domain_elim Hwf0)
        | _ => constr:(Hwf0) end in
      let cd := lazymatch Hwf_fact with ?c _ => c end in
      let args := lazymatch Hwf_fact with _ ?a => a end in
      let C := constr:(_ : ZesuCallSliceCaller cd I _ _ _ _ _) in
      let frame := lazymatch type of C with
                   | @ZesuCallSliceCaller _ _ _ _ _ _ _ _ _ ?frame _ _ => frame end in
      let fr := eval cbv beta in (frame args) in
      eapply (@zesu_call_slice_caller_domain _ _ _ _ _ _ _ _ _ _ _ _ C args p l out sp
                (oa - fr)%Z);
      [ exact Hwf
      | exact Hwin
      | cbv beta; zesu_call_slice_address
      | cbv beta; rewrite Houta; clear; zesu_call_slice_lia
      | clear; zesu_call_slice_lia
      | cbv beta;
        first [ reflexivity
              | rewrite ?Z_to_bv_unsigned; apply bv_wrap_small;
                zesu_call_slice_with_ranges zesu_call_slice_lia ]
      | assumption ]
    end
  end.

(* The window facts in the shape a successor restates the call record in:
   the slice length `Z.of_nat (length (take l (drop (p - base) bytes))) = l`
   and the two window bounds. `NamedEquations.zesu_finish_exists_from_hypotheses`
   closes the record's conjuncts by hypotheses of the same head; the window
   itself is a conjunction, which that step does not open. *)
Ltac zesu_call_slice_record_facts Hwin Hrange :=
  let Hlen := fresh "HcsLength" in
  let Hlow := fresh "HcsWindowLow" in
  let Hhigh := fresh "HcsWindowHigh" in
  try pose proof (zesu_call_slice_window_length _ _ _ _ Hwin (proj1 Hrange)) as Hlen;
  pose proof (proj1 Hwin) as Hlow;
  pose proof (proj2 Hwin) as Hhigh.

(* The rest of the step once the slice is held as "HcsSlice": the output
   slot, the existential's witnesses, the callee's domain (proved once by the
   caller's lemma on the window `Hwin`, after `prep`, and kept as a
   hypothesis) and the callee's stack pointer over the caller's root word. *)
Ltac zesu_call_slice_hand I Hwin out sp size count slice prep :=
  zesu_call_slice_out_slot out size count ltac:(fun oa before Houta =>
    rewrite Houta;
    iExists (li_pair before (li_pair slice tt));
    cbv [li_fst li_snd];
    iSplitL "HcsSlice"; [iExact "HcsSlice"|];
    iSplitL "HcsOutArray"; [iExact "HcsOutArray"|];
    lazymatch goal with
    | |- environments.envs_entails _ (⌜?D⌝ ∗ _)%I =>
        let Hd := fresh "HcsDomain" in
        assert (Hd : D) by (prep tt; zesu_call_slice_domain I Hwin Houta oa);
        iSplitR; [iPureIntro; exact Hd|]
    end;
    (* the callee's stack pointer as an integer over the caller's root
       word: the callee hands its scratch region back there *)
    let rsp := zesu_call_slice_root sp in
    let rz := zesu_call_slice_root_z rsp in
    let dsp := zesu_call_slice_eval_at rsp constr:((bv_unsigned sp - rz)%Z) in
    lazymatch dsp with
    | Z0 => idtac
    | _ =>
        let spz := lazymatch dsp with
          | Zneg ?q => constr:((rz - Zpos q)%Z)
          | _ => constr:((rz + dsp)%Z)
          end in
        let Hspeq := fresh "HcsSpEq" in
        assert (Hspeq : bv_unsigned sp = spz) by zesu_call_slice_address;
        pose proof (Hspeq : zesu_call_slice_addr_fact (bv_unsigned sp = spz))
    end).

Ltac zesu_call_slice :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ ?T ?body) =>
    let dummy := lazymatch T with
      | li_prod (list ?A) (li_prod (list ?B) unit) =>
          constr:(li_pair (@nil A) (li_pair (@nil B) tt))
      end in
    let opened := eval cbv beta iota delta [li_fst li_snd] in (body dummy) in
    lazymatch opened with
    | ((bv_unsigned ?p ↦ₘ∗ _) ∗ (bv_unsigned ?out ↦ₘ∗ _) ∗
        ⌜?dom (?mk (_ :: _ :: ?l :: _) ?sp _ _ _)⌝ ∗ _)%I =>
      let I := constr:(_ : ZesuCallSliceInterface dom _) in
      let meaning := lazymatch type of I with @ZesuCallSliceInterface _ _ _ ?m => m end in
      let count := eval vm_compute in (@zesu_call_slice_out_size _ _ _ _ I) in
      let size := eval vm_compute in (Z.of_nat count) in
      zesu_call_slice_payload_windows I dom meaning mk;
      iMatchHyp ltac:(fun Harray resource =>
        lazymatch resource with
        | (?base ↦ₘ∗ ?bytes)%I =>
          zesu_call_slice_window I dom meaning mk p l base bytes ltac:(fun Hw =>
            let Hwin := fresh "HcsWindow" in
            pose proof Hw as Hwin;
            let len := lazymatch type of Hwin with (_ /\ (_ <= _ + Z.of_nat ?len)%Z) => len end in
            let start := constr:(Z.to_nat (bv_unsigned p - base)) in
            let cnt := constr:(Z.to_nat (bv_unsigned l)) in
            let Hrange := fresh "HcsRange" in
            pose proof (bv_unsigned_in_range _ l) as Hrange;
            let Haddr := fresh "HcsAddress" in
            assert (Haddr : (base + Z.of_nat start = bv_unsigned p)%Z)
              by (clear -Hwin; zesu_call_slice_lia);
            let Hbounds := fresh "HcsBounds" in
            assert (Hbounds : (start + cnt <= len)%nat)
              by (clear -Hwin Hrange; zesu_call_slice_lia);
            zesu_call_slice_record_facts Hwin Hrange;
            iRename Harray into "HcsArray";
            iDestruct (zesu_byte_array_lend_slice _ bytes start cnt Hbounds with "HcsArray")
              as "[HcsSlice HcsRestore]";
            iEval (rewrite Haddr) in "HcsSlice HcsRestore";
            zesu_call_slice_hand I Hwin out sp size count
              constr:(take cnt (drop start bytes)) ltac:(fun _ => idtac))
        end)
    end
  end.

(* A call on the whole of a held array: the array sits at exactly
   `bv_unsigned p` and its length is `bv_unsigned l`. Lithium's own step
   would hand the array over and prove the callee's domain without keeping
   it, so this runs first (`Finish.zesu_run_pass_v1`). The window is the
   array itself, offset 0 and full length (`zesu_call_slice_take_drop_whole`);
   the domain is proved once on that window by the caller's lemma and kept,
   as for a slice, and the array goes to the callee whole (nothing to
   restore). *)
Ltac zesu_call_slice_whole :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ ?T ?body) =>
    let dummy := lazymatch T with
      | li_prod (list ?A) (li_prod (list ?B) unit) =>
          constr:(li_pair (@nil A) (li_pair (@nil B) tt))
      end in
    let opened := eval cbv beta iota delta [li_fst li_snd] in (body dummy) in
    lazymatch opened with
    | ((bv_unsigned ?p ↦ₘ∗ _) ∗ (bv_unsigned ?out ↦ₘ∗ _) ∗
        ⌜?dom (?mk (_ :: _ :: ?l :: _) ?sp _ _ _)⌝ ∗ _)%I =>
      let I := constr:(_ : ZesuCallSliceInterface dom _) in
      let count := eval vm_compute in (@zesu_call_slice_out_size _ _ _ _ I) in
      let size := eval vm_compute in (Z.of_nat count) in
      iMatchHyp ltac:(fun Harray resource =>
        lazymatch resource with
        | (?base ↦ₘ∗ ?bytes)%I =>
          constr_eq base (bv_unsigned p);
          let Hlen := fresh "HcsWholeLength" in
          assert (Hlen : Z.of_nat (length bytes) = bv_unsigned l)
            by first [assumption | symmetry; assumption];
          let Hwin := fresh "HcsWindow" in
          assert (Hwin : (base <= bv_unsigned p /\
                          bv_unsigned p + bv_unsigned l <= base + Z.of_nat (length bytes))%Z)
            by (clear - Hlen; zesu_call_slice_lia);
          let Hrange := fresh "HcsRange" in
          pose proof (bv_unsigned_in_range _ l) as Hrange;
          zesu_call_slice_record_facts Hwin Hrange;
          let Hwhole := fresh "HcsWhole" in
          pose proof (zesu_call_slice_take_drop_whole base _ bytes Hlen) as Hwhole;
          iRename Harray into "HcsSlice";
          zesu_call_slice_hand I Hwin out sp size count bytes
            ltac:(fun _ => rewrite <- Hwhole)
        end)
    end
  end.

Ltac zesu_call_slice_whole_step :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ (li_prod (list _) (li_prod (list _) unit)) _) =>
      let _ := constr:(_ : ZesuStepInteriorByteSlice) in
      ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_call_slice_whole
  end.

(* The address of a held memory resource. *)
Ltac zesu_call_slice_resource_address res :=
  lazymatch res with
  | (?a ↦ₘ∗ _)%I => a
  | (?a ↦ₘ? _)%I => a
  | (?a ↦ₘ _)%I => a
  end.

(* Restate the address `a` of the held resource `H` as the address `b` the
   goal requests, when both are closed-offset chains of the same root word
   and their difference is the numeral 0 (proved over the range facts). A
   difference that mentions anything but the root is refused before any
   evaluation (`vm_compute` of an open term can grow without bound). *)
Ltac zesu_call_restate_at H a b ra :=
  let rb := zesu_call_slice_root b in
  constr_eq ra rb;
  let f := eval pattern ra in ((a - b)%Z) in
  lazymatch f with ?g _ => ZesuSsz.Automation2.VmClosed.zesu_closed_term g end;
  let d := zesu_call_slice_eval_at ra constr:((a - b)%Z) in
  lazymatch d with 0%Z => idtac end;
  let Hab := fresh "HcsRestate" in
  assert (Hab : a = b) by zesu_call_slice_address;
  iRename H into "HcsMoved";
  iEval (rewrite Hab) in "HcsMoved"; clear Hab;
  iDestruct "HcsMoved" as "?".

(* The resources a callee hands back are addressed over its own stack
   pointer word `w` (`bv_unsigned (w + 400 + c)`), the caller's successor
   asks for them over the caller's root (`bv_unsigned root - 400 + …`): each
   held resource whose address mentions `w` and that the goal does not
   request at that address is restated at the address the goal requests at
   the same place. Fails when nothing is restated. *)
Ltac zesu_call_restate_returned w :=
  progress repeat (lazymatch goal with
  | |- environments.envs_entails _ ?G =>
      iMatchHyp ltac:(fun H res =>
        let a := zesu_call_slice_resource_address res in
        lazymatch a with context [w] => idtac end;
        lazymatch G with
        | context [(a ↦ₘ∗ _)%I] => fail
        | context [(a ↦ₘ? _)%I] => fail
        | context [(a ↦ₘ _)%I] => fail
        | _ => idtac
        end;
        let ra := zesu_call_slice_root a in
        match G with
        | context [(?b ↦ₘ∗ _)%I] => zesu_call_restate_at H a b ra
        | context [(?b ↦ₘ? _)%I] => zesu_call_restate_at H a b ra
        | context [(?b ↦ₘ _)%I] => zesu_call_restate_at H a b ra
        end)
  end).

(* The stack pointer word of a callee that has returned, until the
   resources it handed back are restated (`zesu_call_restate_step`). *)
Definition zesu_call_returned_frame (w : bv 64) : Prop := True.

(* The slice the callee returned goes back into the array it was lent from;
   the addresses the callee states over its own stack pointer are restated
   over the caller's root word, and the callee's stack pointer word is kept
   as a `zesu_call_returned_frame` marker. The returned slice may carry the
   callee's element type (`byte`) where the lend wrote `bv 8`: it is matched
   up to conversion once the address agrees syntactically. *)
Ltac zesu_call_restore :=
  iMatchHyp ltac:(fun Hr res =>
    lazymatch res with
    | (?borrowed -∗ (_ ↦ₘ∗ _))%I =>
        lazymatch borrowed with (?ba ↦ₘ∗ _)%I =>
        iMatchHyp ltac:(fun Hs returned =>
          lazymatch returned with (?ra ↦ₘ∗ _)%I =>
          constr_eq ra ba;
          first [constr_eq returned borrowed | unify returned borrowed];
          iRename Hr into "HcsR"; iRename Hs into "HcsS";
          iDestruct ("HcsR" with "HcsS") as "?" end) end
    end);
  try (lazymatch goal with
       | H : zesu_call_slice_addr_fact (@bv_unsigned _ ?w = _) |- _ =>
           pose proof (I : zesu_call_returned_frame w)
       end);
  repeat match goal with
  | H : zesu_call_slice_addr_fact (?a = ?b) |- _ => rewrite (H : a = b); clear H
  end.

(* At an existential whose first resource is requested at an address no
   held resource has in that spelling, while a returned-frame marker is in
   the context: restate what the callee handed back
   (`zesu_call_restate_returned`) and drop the marker. *)
Ltac zesu_call_restate_step :=
  match goal with
  | Hm : zesu_call_returned_frame ?w |- environments.envs_entails _ (@bi_exist _ _ ?body) =>
      let b := lazymatch body with
        | (fun _ => ((?b ↦ₘ∗ _) ∗ _)%I) => b
        | (fun _ => ((?b ↦ₘ _) ∗ _)%I) => b
        end in
      assert_fails (iMatchHyp ltac:(fun _ res =>
        let a := zesu_call_slice_resource_address res in constr_eq a b));
      zesu_call_restate_returned w; clear Hm
  end.

(* A callee that takes its input slice by reference
   (`ZesuCallSliceRefCaller`). At the existential its call spec asks for,
     ∃ x, bv_unsigned r ↦ₘ x.3 ∗ (bv_unsigned r + 8) ↦ₘ x.2 ∗
          bv_unsigned x.3 ↦ₘ∗ x.1 ∗ bv_unsigned out ↦ₘ? n ∗
          ⌜length x.1 = bv_unsigned x.2⌝ ∗ ⌜domain (mk argv sp x.3 _ x.1)⌝ ∗ …,
   the step reads the two words the caller stored at r (as cells or as the
   byte cells of a store), finds the window of the slice in the caller's input
   by the window steps above, lends it, cuts the output slot out of an
   uninitialised region, and proves the length and the callee's domain. *)

(* The little-endian bytes of a word as one byte array, as the word's cell. *)
Lemma zesu_call_slice_word_array `{!islaG Sigma} (a : Z) (w : bv 64) :
  a ↦ₘ∗ ZesuSsz.Automation2.ByteExtractCodec281.byte_extracts281 8 w -∗ a ↦ₘ w.
Proof.
  iIntros "Harray".
  iDestruct (ZesuSsz.Contracts.IslarisMemory.mem_mapsto_byte_array_to_mapsto with "Harray")
    as "Hw".
  rewrite ZesuSsz.Automation2.ByteExtractCodec281.byte_extracts_codec281.
  rewrite length_bv_to_little_endian; [|zesu_call_slice_lia].
  rewrite little_endian_to_bv_to_little_endian; [|zesu_call_slice_lia].
  change (Z.to_N (Z.to_nat 8) * 8)%N with 64%N.
  rewrite Z.mod_small; [|pose proof (bv_unsigned_in_range _ w) as Hw;
    unfold bv_modulus in Hw; cbn in *; zesu_call_slice_lia].
  rewrite Z_to_bv_bv_unsigned. iExact "Hw".
Qed.

(* Eight byte cells holding the little-endian bytes of a word, as the word's
   cell. *)
Lemma zesu_call_slice_word_cells `{!islaG Sigma} (a : Z) (w : bv 64) :
  ((a + Z.of_nat 0 * 1) ↦ₘ bv_extract 0 8 w ∗ (a + Z.of_nat 1 * 1) ↦ₘ bv_extract 8 8 w ∗
   (a + Z.of_nat 2 * 1) ↦ₘ bv_extract 16 8 w ∗ (a + Z.of_nat 3 * 1) ↦ₘ bv_extract 24 8 w ∗
   (a + Z.of_nat 4 * 1) ↦ₘ bv_extract 32 8 w ∗ (a + Z.of_nat 5 * 1) ↦ₘ bv_extract 40 8 w ∗
   (a + Z.of_nat 6 * 1) ↦ₘ bv_extract 48 8 w ∗ (a + Z.of_nat 7 * 1) ↦ₘ bv_extract 56 8 w ∗
   emp) -∗
  a ↦ₘ w.
Proof.
  iIntros "Hcells". iApply zesu_call_slice_word_array.
  rewrite mem_mapsto_array_eq /mem_mapsto_array_def.
  iExists 1%N. iSplit; [done|].
  iDestruct "Hcells" as "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _)".
  iDestruct (mem_mapsto_in_range with "H0") as %Hr0.
  iDestruct (mem_mapsto_in_range with "H7") as %Hr7.
  iSplit; [iPureIntro; cbn in *; zesu_call_slice_lia|].
  cbn. iFrame.
Qed.

(* `size` bytes at distance `d` of an uninitialised region, as their own
   region. *)
Lemma zesu_call_slice_uninit_cut `{!islaG Sigma} (a d n size : Z) :
  0 <= d -> 0 <= size -> d + size <= n ->
  a ↦ₘ? n -∗ a ↦ₘ? d ∗ (a + d) ↦ₘ? size ∗ (a + d + size) ↦ₘ? (n - d - size).
Proof.
  iIntros (Hd Hsize Hn) "H".
  iDestruct (mem_mapsto_uninit_split d with "H") as "[$ H]"; [zesu_call_slice_lia|].
  iDestruct (mem_mapsto_uninit_split size with "H") as "[$ H]"; [zesu_call_slice_lia|].
  iExact "H".
Qed.

(* The word the caller stored at `addr`: a cell, the eight byte cells a
   store left, or the byte array of its little-endian bytes. Renames it to
   `name` (`addr ↦ₘ w`) and passes `w` to `k`. *)
Ltac zesu_call_slice_ref_word addr name k :=
  let raddr := zesu_call_slice_root addr in
  iMatchHyp ltac:(fun H res =>
    let w := lazymatch res with
      | (((?a + Z.of_nat 0 * 1) ↦ₘ bv_extract 0 8 ?w) ∗ _)%I => w
      | (?a ↦ₘ∗ (bv_extract 0 8 ?w :: _))%I => w
      | (?a ↦ₘ ?w)%I => lazymatch type of w with bv 64 => w end
      end in
    let a := lazymatch res with
      | (((?a + Z.of_nat 0 * 1) ↦ₘ _) ∗ _)%I => a
      | (?a ↦ₘ∗ _)%I => a
      | (?a ↦ₘ _)%I => a
      end in
    let ra := zesu_call_slice_root a in
    constr_eq raddr ra;
    let d := zesu_call_slice_eval_at raddr constr:((addr - a)%Z) in
    lazymatch d with 0%Z => idtac end;
    let Ha := fresh "HcsRefAddr" in
    assert (Ha : addr = a) by zesu_call_slice_address;
    iRename H into "HcsRefCells";
    lazymatch res with
    | (_ ∗ _)%I => iDestruct (zesu_call_slice_word_cells a w with "HcsRefCells") as name
    | (_ ↦ₘ∗ _)%I => iDestruct (zesu_call_slice_word_array a w with "HcsRefCells") as name
    | _ => iRename "HcsRefCells" into name
    end;
    iEval (rewrite -Ha) in name; clear Ha;
    k w).

Ltac zesu_call_slice_ref :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ ?T ?body) =>
    let dummy := lazymatch T with
      | li_prod (list ?A) (li_prod (bv 64) (li_prod (bv 64) unit)) =>
          constr:(li_pair (@nil A) (li_pair (bv_0 64) (li_pair (bv_0 64) tt)))
      end in
    let opened := eval cbv beta iota delta [li_fst li_snd] in (body dummy) in
    lazymatch opened with
    | ((bv_unsigned ?r ↦ₘ _) ∗ ((bv_unsigned ?r + 8) ↦ₘ _) ∗ (bv_unsigned _ ↦ₘ∗ _) ∗
        (bv_unsigned ?out ↦ₘ? ?size0) ∗ ⌜_⌝ ∗ ⌜?dom (?mk ?argv ?sp _ _ _)⌝ ∗ _)%I =>
      let rest := lazymatch argv with _ :: _ :: ?rest => rest end in
      match goal with
      | Hwf : ?cd ?args |- _ =>
        let C := constr:(_ : ZesuCallSliceRefCaller cd dom mk _ _ _ _ _ _) in
        lazymatch type of C with
        | @ZesuCallSliceRefCaller _ _ _ _ _ ?inputBase ?inputBytes ?frame _ _ _ =>
        let base := eval cbv beta in (inputBase args) in
        let bytes := eval cbv beta in (inputBytes args) in
        let fr := eval cbv beta in (frame args) in
        zesu_call_slice_ref_word constr:(bv_unsigned r) "HcsRefP" ltac:(fun p =>
        zesu_call_slice_ref_word constr:((bv_unsigned r + 8)%Z) "HcsRefL" ltac:(fun l =>
        (* the window of (p, l): the window steps of a by-value callee whose
           call record the context holds, a stated window, or the rest the
           previous by-reference call returned *)
        let Hwin := fresh "HcsWindow" in
        once (zesu_call_slice_window_any p l base bytes
                ltac:(fun Hw => pose proof Hw as Hwin));
        let start := constr:(Z.to_nat (bv_unsigned p - base)) in
        let cnt := constr:(Z.to_nat (bv_unsigned l)) in
        let Hrange := fresh "HcsRange" in
        pose proof (bv_unsigned_in_range _ l) as Hrange;
        let Haddr := fresh "HcsAddress" in
        assert (Haddr : (base + Z.of_nat start = bv_unsigned p)%Z)
          by (clear -Hwin; zesu_call_slice_lia);
        let Hbounds := fresh "HcsBounds" in
        assert (Hbounds : (start + cnt <= length bytes)%nat)
          by (clear -Hwin Hrange; zesu_call_slice_lia);
        zesu_call_slice_record_facts Hwin Hrange;
        iMatchHyp ltac:(fun Harray resource =>
          lazymatch resource with
          | (?b ↦ₘ∗ ?bs)%I => constr_eq b base; constr_eq bs bytes;
              iRename Harray into "HcsArray"
          end);
        iDestruct (zesu_byte_array_lend_slice _ bytes start cnt Hbounds with "HcsArray")
          as "[HcsSlice HcsRestore]";
        iEval (rewrite Haddr) in "HcsSlice HcsRestore";
        (* the output slot, cut out of an uninitialised region *)
        let rout := zesu_call_slice_root out in
        let size := eval vm_compute in size0 in
        iMatchHyp ltac:(fun Hu resource2 =>
          lazymatch resource2 with
          | (?ua ↦ₘ? ?n0)%I =>
              let rua := zesu_call_slice_root ua in
              constr_eq rout rua;
              let d := zesu_call_slice_eval_at rout constr:((bv_unsigned out - ua)%Z) in
              let n := zesu_call_slice_eval_at rout n0 in
              let fits := eval vm_compute in ((0 <=? d)%Z && (d + size <=? n)%Z) in
              lazymatch fits with true => idtac end;
              iRename Hu into "HcsU";
              tryif constr_eq n0 n then idtac
              else (let Hn := fresh "HcsSize" in
                    assert (Hn : n0 = n) by zesu_call_slice_address;
                    iEval (rewrite Hn) in "HcsU"; clear Hn);
              let Houta := fresh "HcsOut" in
              assert (Houta : bv_unsigned out = (ua + d)%Z) by zesu_call_slice_address;
              iDestruct (zesu_call_slice_uninit_cut ua d n size with "HcsU")
                as "(HcsU0 & HcsOutRegion & HcsU1)";
              [clear; zesu_call_slice_lia|clear; zesu_call_slice_lia|
               clear; zesu_call_slice_lia|];
              let r1 := eval vm_compute in (n - d - size)%Z in
              change (n - d - size)%Z with r1;
              lazymatch d with 0%Z => iClear "HcsU0"; iEval (rewrite Z.add_0_r) in "HcsU1"
                         | _ => idtac end;
              lazymatch r1 with 0%Z => iClear "HcsU1" | _ => idtac end;
              iEval (rewrite -Houta) in "HcsOutRegion";
              let k := zesu_call_slice_eval_at rout constr:((bv_unsigned out - fr)%Z) in
              let j := zesu_call_slice_eval_at rout constr:((bv_unsigned r - fr)%Z) in
              iExists (li_pair (take cnt (drop start bytes)) (li_pair l (li_pair p tt)));
              cbv [li_fst li_snd];
              iSplitL "HcsRefP"; [iExact "HcsRefP"|];
              iSplitL "HcsRefL"; [iExact "HcsRefL"|];
              iSplitL "HcsSlice"; [iExact "HcsSlice"|];
              iSplitL "HcsOutRegion"; [iExact "HcsOutRegion"|];
              iSplitR; [iPureIntro;
                        exact (zesu_call_slice_window_length _ _ _ _ Hwin (proj1 Hrange))|];
              lazymatch goal with
              | |- environments.envs_entails _ (⌜?D⌝ ∗ _)%I =>
                  let Hd := fresh "HcsDomain" in
                  assert (Hd : D)
                    by (eapply (@zesu_call_slice_ref_caller_domain _ _ _ _ _ _ _ _ _ _ _ C
                                  args out r p l sp k j rest);
                        [ exact Hwf
                        | exact Hwin
                        | cbv beta; zesu_call_slice_address
                        | cbv beta; zesu_call_slice_address
                        | clear; zesu_call_slice_lia
                        | cbv beta; zesu_call_slice_address
                        | clear; zesu_call_slice_lia
                        | clear; zesu_call_slice_lia ]);
                  iSplitR; [iPureIntro; exact Hd|]
              end;
              (* the callee's stack pointer as an integer over the caller's
                 root word, as in `zesu_call_slice` *)
              let rsp := zesu_call_slice_root sp in
              let rz := zesu_call_slice_root_z rsp in
              let dsp := zesu_call_slice_eval_at rsp constr:((bv_unsigned sp - rz)%Z) in
              lazymatch dsp with
              | Z0 => idtac
              | _ =>
                  let spz := lazymatch dsp with
                    | Zneg ?q => constr:((rz - Zpos q)%Z)
                    | _ => constr:((rz + dsp)%Z)
                    end in
                  let Hspeq := fresh "HcsSpEq" in
                  assert (Hspeq : bv_unsigned sp = spz) by zesu_call_slice_address;
                  pose proof (Hspeq : zesu_call_slice_addr_fact (bv_unsigned sp = spz))
              end
          end)))
        end
      end
    end
  end.

(* The step at the existential a call spec asks for; it runs where the
   interior-slice lend runs and before it (`Finish.zesu_run_pass_v1`).
   Lithium may have let-bound the proof-mode environment (`IPM_JANNO`): the
   step reads the held arrays, so it first substitutes that binding back, as
   the interior-slice lend does. A pointer or length argument the caller
   stored byte by byte and reloaded is read as the word it came from. *)
Ltac zesu_call_slice_step :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ _ _) =>
      let _ := constr:(_ : ZesuStepInteriorByteSlice) in
      ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      try ZesuSsz.Automation2.WrappedWord.zesu_word_explicit_list_rewrite;
      first [zesu_call_slice | zesu_call_slice_ref | zesu_call_restore]
  end.
(* The by-reference step before Lithium's own step: when the slice record's
   pointer word sits in a held byte array, Lithium reads the first cell of
   the call spec out of it as the little-endian value of the bytes and leaves
   no shape for the by-reference step to match. *)
Ltac zesu_call_slice_ref_first :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ _ ?body) =>
      lazymatch body with
      | (fun _ => ((bv_unsigned _ ↦ₘ _) ∗ ((bv_unsigned _ + 8) ↦ₘ _) ∗ _)%I) => idtac
      end;
      let _ := constr:(_ : ZesuStepInteriorByteSlice) in
      ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      (* Lithium let-binds the record's address: the step compares it with
         the addresses of the held cells. *)
      repeat match goal with
      | L := _ |- environments.envs_entails _ ?G =>
          lazymatch G with context [L] => unfold L end
      end;
      zesu_call_slice_ref
  end.
(* Early restore: at any existential goal with a restore wand and its
   returned slice in the context, before Lithium's own step; then, at an
   existential that asks for a resource in another spelling, the callee's
   returned resources are restated (`zesu_call_restate_step`). *)
Ltac zesu_call_early_restore :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ _ _) =>
      first [zesu_call_restore | zesu_call_restate_step]
  end.
