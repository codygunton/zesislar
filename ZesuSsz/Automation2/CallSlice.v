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
   hypothesis (`DomainRanges.v`). *)
Ltac zesu_call_slice_with_ranges tac :=
  match goal with
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
            | assert (Hlt : (bv_unsigned l < limit)%Z) by (eauto 3) ];
            k constr:((@zesu_call_slice_payload_in_input_load _ _ _ _ I _ _ _ _ _ _ _ _ Hmean
                         (zesu_call_slice_unsigned_pos _ l Hnz) Hlt) :
                       (base <= bv_unsigned p /\
                        bv_unsigned p + bv_unsigned l <= base + Z.of_nat (length bytes))%Z)
        end
      end
    end
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
    | Hwf : ?cd ?args |- _ =>
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
            iRename Harray into "HcsArray";
            iDestruct (zesu_byte_array_lend_slice _ bytes start cnt Hbounds with "HcsArray")
              as "[HcsSlice HcsRestore]";
            iEval (rewrite Haddr) in "HcsSlice HcsRestore";
            zesu_call_slice_out_slot out size count ltac:(fun oa before Houta =>
              rewrite Houta;
              iExists (li_pair before (li_pair (take cnt (drop start bytes)) tt));
              cbv [li_fst li_snd];
              iSplitL "HcsSlice"; [iExact "HcsSlice"|];
              iSplitL "HcsOutArray"; [iExact "HcsOutArray"|];
              lazymatch goal with
              | |- environments.envs_entails _ (⌜?D⌝ ∗ _)%I =>
                  let Hd := fresh "HcsDomain" in
                  assert (Hd : D) by zesu_call_slice_domain I Hwin Houta oa;
                  iSplitR; [iPureIntro; exact Hd|]
              end;
              (* the callee's stack pointer as an integer over the caller's
                 root word: the callee hands its scratch region back there *)
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
              end))
        end)
    end
  end.

(* The slice the callee returned goes back into the array it was lent from;
   the addresses the callee states over its own stack pointer are restated
   over the caller's root word. *)
Ltac zesu_call_restore :=
  iMatchHyp ltac:(fun Hr res =>
    lazymatch res with
    | (?borrowed -∗ (_ ↦ₘ∗ _))%I =>
        iMatchHyp ltac:(fun Hs returned =>
          constr_eq returned borrowed;
          iRename Hr into "HcsR"; iRename Hs into "HcsS";
          iDestruct ("HcsR" with "HcsS") as "?")
    end);
  repeat match goal with
  | H : zesu_call_slice_addr_fact (?a = ?b) |- _ => rewrite (H : a = b); clear H
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
      first [zesu_call_slice | zesu_call_restore]
  end.
(* Early restore: at any existential goal with a restore wand and its
   returned slice in the context, before Lithium's own step. *)
Ltac zesu_call_early_restore :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ _ _) => zesu_call_restore
  end.
