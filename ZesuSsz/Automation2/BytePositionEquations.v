From Coq Require Import ZArith.ZArith Lists.List NArith.NArith Lia.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require ZesuSsz.Automation2.VmClosed.
Require ZesuSsz.Automation2.WrappedWord.
Local Open Scope Z_scope.

(* Specs state a value loaded from a byte list as byte positions of the list:
   `nth k L 0`, and for a load of c bytes at k the byte concatenation
   `bv_concat (8 * c) (... (bv_concat 16 (nth (k+c-1) L 0) (nth (k+c-2) L 0)) ...) (nth k L 0)`.
   The block state holds the same value as a window
   `Z_to_bv (8 * c) (little_endian_to_bv 8 (take c (drop k L)))`, or as a byte
   variable v with `L !! k = Some v`. When the list on the spec side is still a
   Lithium existential, the equation between the two forms stops Lithium:
   unification cannot see the list through the window or the variable. The
   step below rewrites the window into the concatenation and the variable into
   its position, after which unification sets the existential. The window
   identity holds for any list (nth defaults to 0 past the end), so the
   rewrite needs no length fact. *)

Lemma zesu_le_window_byte (k : nat) (bytes : list (bv 8)) :
  Z_to_bv 8 (little_endian_to_bv 8 (take 1 (drop k bytes))) = nth k bytes (BV 8 0).
Proof.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  revert bytes; induction k as [|k IH]; intros [|b bytes]; cbn; try done.
  - unfold little_endian_to_bv; cbn. rewrite Z.shiftl_0_l Z.lor_0_r.
    apply bv_wrap_small. apply bv_unsigned_in_range.
  - apply IH.
Qed.

Lemma zesu_le_window_concat (n m : N) (count k : nat) (bytes : list (bv 8)) :
  n = (m + 8)%N ->
  Z_to_bv n (little_endian_to_bv 8 (take (S count) (drop k bytes))) =
  bv_concat n (Z_to_bv m (little_endian_to_bv 8 (take count (drop (S k) bytes))))
    (nth k bytes (BV 8 0)).
Proof.
  intros ->.
  assert (Hshape : forall (rest : list (bv 8)) (first : bv 8),
    Z_to_bv (m + 8) (little_endian_to_bv 8 (first :: rest)) =
    bv_concat (m + 8) (Z_to_bv m (little_endian_to_bv 8 rest)) first).
  { intros rest first. apply bv_eq.
    rewrite bv_concat_unsigned' !Z_to_bv_unsigned. unfold little_endian_to_bv; cbn [fmap list_fmap little_endian_to_Z].
    set (E := little_endian_to_Z (Z.of_N 8) (bv_unsigned <$> rest)).
    unfold bv_wrap, bv_modulus.
    apply Z.bits_inj'. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_N (m + 8))) as [Hlt|Hge].
    2: { rewrite !Z.mod_pow2_bits_high; [done|lia|lia]. }
    rewrite !Z.mod_pow2_bits_low; [|lia|lia].
    rewrite !Z.lor_spec orb_comm. f_equal.
    change (Z.of_N 8) with 8. rewrite !Z.shiftl_spec; [|lia|lia].
    destruct (Z.ltb_spec (i - 8) 0).
    { rewrite !Z.testbit_neg_r; [done|lia|lia]. }
    rewrite Z.mod_pow2_bits_low; [done|lia]. }
  assert (Hempty : Z_to_bv (m + 8) (little_endian_to_bv 8 (@nil (bv 8))) =
    bv_concat (m + 8) (Z_to_bv m (little_endian_to_bv 8 (take count (@nil (bv 8))))) (BV 8 0)).
  { rewrite take_nil. transitivity (Z_to_bv (m + 8) (little_endian_to_bv 8 [BV 8 0]));
      [reflexivity | apply Hshape]. }
  revert bytes; induction k as [|k IH]; intros [|b bytes].
  - exact Hempty.
  - cbn [drop take nth]. apply Hshape.
  - exact Hempty.
  - cbn [drop nth]. apply IH.
Qed.

(* The concatenation of the c bytes at k, most significant byte innermost.
   Positions are built at `bv 8` whatever the list's element type: at a
   contract byte type (`bits 8`, i.e. `bv (Z_idx 8)`) the concatenation's
   widths were inferred as `Z_idx 8`, and the result no longer matched the
   goal's `bv_concat 16 8 8` syntactically (decodeParentHeader 0568). *)
Ltac zesu_le_window_bytes width count start bytes :=
  lazymatch count with
  | 1%nat => constr:(@nth (bv 8) start bytes (BV 8 0))
  | S ?rest =>
      let inner_width := eval vm_compute in (width - 8)%N in
      let inner := zesu_le_window_bytes inner_width rest (S start) bytes in
      constr:(bv_concat width inner (@nth (bv 8) start bytes (BV 8 0)))
  end.

Ltac zesu_le_window_prove :=
  repeat match goal with
  | |- context [Z_to_bv 8 (little_endian_to_bv 8 (take 1 (drop ?start ?bytes)))] =>
      rewrite (zesu_le_window_byte start bytes)
  | |- context [Z_to_bv ?width (little_endian_to_bv 8 (take (S ?rest) (drop ?start ?bytes)))] =>
      let inner_width := eval vm_compute in (width - 8)%N in
      rewrite (zesu_le_window_concat width inner_width rest start bytes eq_refl)
  end; reflexivity.

(* Prove the concatenation form of one window whose width is 8 bits per byte,
   with a closed count of at least one and a closed start, and pass the
   equation to [location]. *)
Ltac zesu_le_window_equation width count start bytes location :=
  ZesuSsz.Automation2.VmClosed.zesu_vm_closed start;
  let c := eval vm_compute in count in
  let k := eval vm_compute in start in
  let w := eval vm_compute in width in
  lazymatch eval vm_compute in
    (bool_decide (w = 8 * N.of_nat c)%N && bool_decide (1 <= c)%nat)%bool with
  | true => idtac end;
  let window := constr:(Z_to_bv width (little_endian_to_bv 8 (take count (drop start bytes)))) in
  let concat := zesu_le_window_bytes w c k bytes in
  let Hwindow := fresh "Hwindow" in
  assert (Hwindow : window = concat) by
    (change window with (Z_to_bv w (little_endian_to_bv 8 (take c (drop k bytes))));
     zesu_le_window_prove);
  location Hwindow;
  clear Hwindow.

Ltac zesu_le_window_rewrite_one :=
  match goal with
  | |- context [Z_to_bv ?width (little_endian_to_bv 8 (take ?count (drop ?start ?bytes)))] =>
      zesu_le_window_equation width count start bytes ltac:(fun Hwindow => rewrite Hwindow)
  end.

(* The same rewrite in an equation or disequation hypothesis (a branch fact
   on a loaded value) while the goal reads the list by byte positions, so
   that the fact states the value as the goal does. A start that is a word
   offset chain becomes a literal first. *)
Ltac zesu_le_window_rewrite_hypothesis :=
  match goal with
  | Hfact : context [Z_to_bv ?width (little_endian_to_bv 8 (take ?count (drop ?start ?bytes)))] |- _ =>
      lazymatch type of Hfact with
      | _ = _ => idtac
      | not (_ = _) => idtac
      end;
      lazymatch goal with |- context [@nth (bv 8) _ bytes _] => idtac end;
      first [
        zesu_le_window_equation width count start bytes ltac:(fun Hwindow => rewrite Hwindow in Hfact)
      | lazymatch start with
        | Z.to_nat ?expression =>
            ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_literal expression
              ltac:(fun Hindex => rewrite Hindex in Hfact)
        end ]
  end.

(* The bytes of a window are opaque when their head normal form is no list
   constructor (a projection of a call's outcome): their positions `nth k`
   do not compute, so the byte-position spelling is the only one a successor
   can state. Bytes that compute to a list (an image of words) are left to
   the window lemmas of their image. *)
Ltac zesu_le_window_opaque_bytes bytes :=
  let head := eval hnf in bytes in
  lazymatch head with
  | cons _ _ => fail
  | nil => fail
  | _ => idtac
  end.

(* A branch premise `x = w` (or `w = x`) with `x` a variable and `w` a load
   window of opaque bytes: Lithium substitutes `x` by `w` everywhere, the
   block history included, while the generated successors and edge instances
   state the same word by byte positions (decodeParentHeader 046c, 04f8: a
   kept register compared with the word loaded from a call's outcome). The
   window takes the byte-position form before the substitution, so the block
   and its successors hold one spelling. A start that is a word offset chain
   becomes a literal first. Only the head of the premise's sides is tested
   (it runs on every introduced premise), and only a 64-bit word window: a
   narrower load (a 16-bit field of a call's outcome) keeps its variable, whose
   type range later goals use (decodeParentHeader 01e4 and the other
   field-skip return sites). Fails, leaving the goal unchanged, on any other
   premise or when no window is rewritten. *)
Ltac zesu_le_window_var_premise :=
  lazymatch goal with
  | |- (?a = ?b) -> _ =>
      lazymatch constr:((a, b)) with
      | (_, Z_to_bv 64%N (little_endian_to_bv 8 (take _ (drop _ ?bytes)))) =>
          is_var a; zesu_le_window_opaque_bytes bytes
      | (Z_to_bv 64%N (little_endian_to_bv 8 (take _ (drop _ ?bytes))), _) =>
          is_var b; zesu_le_window_opaque_bytes bytes
      end;
      let H := fresh "Hpremise" in
      intros H;
      progress repeat match type of H with
        | context [Z_to_bv ?width (little_endian_to_bv 8 (take ?count (drop ?start ?bytes)))] =>
            first [
              zesu_le_window_equation width count start bytes ltac:(fun Hwindow => rewrite Hwindow in H)
            | lazymatch start with
              | Z.to_nat ?expression =>
                  ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_literal expression
                    ltac:(fun Hindex => rewrite Hindex in H)
              end ]
        end;
      revert H
  end.

(* A branch fact on a word against a closed word, as an equation (or
   disequation) of the word's bv_unsigned, when the goal states that
   bv_unsigned. A zero-extended word states the bv_unsigned of the value it
   extends. *)
Lemma zesu_zero_extend_eq_unsigned (n z : N) (value : bv n) (word : bv z) :
  (n <= z)%N -> bv_zero_extend z value = word -> bv_unsigned value = bv_unsigned word.
Proof. intros Hle <-. rewrite bv_zero_extend_unsigned; [reflexivity | exact Hle]. Qed.

Lemma zesu_zero_extend_neq_unsigned (n z : N) (value : bv n) (word : bv z) :
  (n <= z)%N -> bv_zero_extend z value <> word -> bv_unsigned value <> bv_unsigned word.
Proof.
  intros Hle Hne Heq. apply Hne, bv_eq. rewrite bv_zero_extend_unsigned; [exact Heq | exact Hle].
Qed.

Lemma zesu_word_eq_unsigned (n : N) (value word : bv n) :
  value = word -> bv_unsigned value = bv_unsigned word.
Proof. intros ->. reflexivity. Qed.

Lemma zesu_word_neq_unsigned (n : N) (value word : bv n) :
  value <> word -> bv_unsigned value <> bv_unsigned word.
Proof. intros Hne Heq. apply Hne, bv_eq, Heq. Qed.

Ltac zesu_word_fact_view Hfact value word view :=
  ZesuSsz.Automation2.VmClosed.zesu_vm_closed word;
  lazymatch goal with |- context [bv_unsigned value] => idtac end;
  let unsigned := eval vm_compute in (bv_unsigned word) in
  let Hview := fresh "Hview" in
  pose proof (view Hfact) as Hview;
  change (bv_unsigned word) with unsigned in Hview;
  clear Hfact.

(* The width side condition `n <= z` is closed: it is decided by computing
   `N.leb n z`, never by a context-wide tactic. `congruence` here ran over every
   hypothesis of the block for each zero-extended fact the match tried; on a
   split conjunct with 266 hypotheses one call took over 800 s. *)
Ltac zesu_word_fact_unsigned :=
  match goal with
  | Hfact : @bv_zero_extend ?n ?z ?value = ?word |- _ =>
      zesu_word_fact_view Hfact value word
        constr:(zesu_zero_extend_eq_unsigned n z value word (proj1 (N.leb_le n z) eq_refl))
  | Hfact : not (@bv_zero_extend ?n ?z ?value = ?word) |- _ =>
      zesu_word_fact_view Hfact value word
        constr:(zesu_zero_extend_neq_unsigned n z value word (proj1 (N.leb_le n z) eq_refl))
  | Hfact : @eq (bv ?n) ?value ?word |- _ =>
      zesu_word_fact_view Hfact value word constr:(zesu_word_eq_unsigned n value word)
  | Hfact : not (@eq (bv ?n) ?value ?word) |- _ =>
      zesu_word_fact_view Hfact value word constr:(zesu_word_neq_unsigned n value word)
  end.

(* A byte variable known from a lookup becomes its list position in an
   equation or disequation hypothesis, when the goal reads that position. *)
Ltac zesu_lookup_value_rewrite_hypothesis :=
  match goal with
  | Hlookup : ?bytes !! ?index = Some ?value |- _ =>
      is_var value;
      lazymatch goal with |- context [@nth (bv 8) index bytes _] => idtac end;
      match goal with
      | Hfact : ?fact |- _ =>
          lazymatch fact with
          | _ !! _ = Some _ => fail
          | _ = _ => idtac
          | not (_ = _) => idtac
          end;
          lazymatch fact with context [value] => idtac end;
          rewrite <- (nth_lookup_Some bytes index (BV 8 0) value Hlookup) in Hfact
      end
  end.

(* Final pure goals: the branch facts in the goal's byte-position form. A
   pass's goal reads the list through a bound name, so the run-loop step
   leaves these facts to the finisher. *)
Ltac zesu_byte_position_facts :=
  progress repeat first [zesu_le_window_rewrite_hypothesis | zesu_lookup_value_rewrite_hypothesis
    | zesu_word_fact_unsigned].

(* A byte variable known from a lookup becomes its list position, when the
   left side reads the same position. The goal is `lhs = ?normalized`; the
   replacement is proved apart, so that the variable in the evar's instance
   stays untouched. *)
Ltac zesu_lookup_value_rewrite_one :=
  lazymatch goal with
  | |- ?lhs = _ =>
      match goal with
      | Hvalue : ?bytes !! ?index = Some ?value |- _ =>
          is_var value;
          lazymatch lhs with context [value] => idtac end;
          lazymatch lhs with context [@nth (bv 8) index _ _] => idtac end;
          lazymatch eval pattern value in lhs with
          | ?body _ =>
              let replaced := eval cbv beta in (body (nth index bytes (BV 8 0))) in
              let Hposition := fresh "Hposition" in
              assert (Hposition : lhs = replaced) by
                (rewrite (nth_lookup_Some bytes index (BV 8 0) value Hvalue); reflexivity);
              rewrite Hposition; clear Hposition
          end
      end
  end.

(* A local definition (a trace let) that the left side mentions is unfolded
   in the equation when it holds a window or sits in a window's start; the
   window rewrite and the index step then see the terms. *)
Ltac zesu_byte_position_unfold_let :=
  lazymatch goal with
  | |- ?lhs = _ =>
      match goal with
      | local := ?body |- _ =>
          lazymatch lhs with context [local] => idtac end;
          first [
            lazymatch body with context [little_endian_to_bv _ _] => idtac end
          | match lhs with
            | context [little_endian_to_bv _ (take _ (drop ?start _))] =>
                lazymatch start with context [local] => idtac end
            end ];
          unfold local
      end
  end.

(* The run-loop step: a pure equation at the head of a lazy existential that
   reads byte positions of a list. Lithium's side-condition step refused it
   (the step runs last). *)
Ltac zesu_byte_position_pure_step :=
  lazymatch goal with
  | |- environments.envs_entails _
         (@bi_exist _ (li_prod _ _) (fun x => bi_sep (bi_pure (@?P x)) _)) =>
      lazymatch P with context [@nth (bv 8) _ _ _] => idtac end;
      notypeclasses refine (tac_normalize_goal_and_liex _ _ _ _ _ _);
        [intros ?;
         progress (repeat first [zesu_byte_position_unfold_let
                                | zesu_le_window_rewrite_one
                                | zesu_lookup_value_rewrite_one]);
         reflexivity
        | cbv beta]
  end.

(* A pure equation between a window of a list and that list's byte
   positions: the window rewrite makes both sides the same concatenation. *)
Ltac zesu_le_window_goal :=
  lazymatch goal with
  | |- @eq _ ?lhs ?rhs =>
      lazymatch lhs with
      | context [little_endian_to_bv 8 (take _ (drop _ ?bytes))] =>
          lazymatch rhs with context [@nth (bv 8) _ bytes _] => idtac end
      end
  end;
  progress repeat zesu_le_window_rewrite_one;
  reflexivity.

(* A list position whose element type is another name of `bv 8` (a
   contract's byte type) is restated at `bv 8`, in the goal and in the
   hypotheses: the window rewrite builds its positions at the list's own
   element type, and the rules above match positions syntactically. *)
Ltac zesu_nth_byte_type_normal :=
  progress repeat first [
    match goal with
    | |- context [@nth ?T ?i ?l ?d] =>
        lazymatch T with bv 8%N => fail | _ => idtac end;
        unify T (bv 8%N);
        change (@nth T i l d) with (@nth (bv 8%N) i l d)
    end
  | match goal with
    | H : context [@nth ?T ?i ?l ?d] |- _ =>
        lazymatch T with bv 8%N => fail | _ => idtac end;
        unify T (bv 8%N);
        change (@nth T i l d) with (@nth (bv 8%N) i l d) in H
    end ].

(* A pure (dis)equation on a word's bv_unsigned that a branch fact on the
   word against a closed word states: the fact's bv_unsigned view. The fact
   may be held as a load window: it first takes the goal's byte-position
   form (the window rewrite in hypotheses). *)
Ltac zesu_word_fact_goal :=
  lazymatch goal with
  | |- @eq Z (bv_unsigned _) _ => idtac
  | |- not (@eq Z (bv_unsigned _) _) => idtac
  end;
  try zesu_nth_byte_type_normal;
  repeat zesu_le_window_rewrite_hypothesis;
  try zesu_nth_byte_type_normal;
  progress repeat zesu_word_fact_unsigned;
  assumption.
