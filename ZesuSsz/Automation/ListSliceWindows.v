From Coq Require Import List Lia Arith.
From stdpp Require Import list tactics.

Lemma zesu_take_drop_prefix {A : Type} (before suffix : list A)
    (prefix start count : nat) :
  (start + count <= prefix)%nat ->
  (prefix <= List.length before)%nat ->
  take count (drop start (take prefix before ++ suffix)) =
    take count (drop start before).
Proof.
  intros Hwindow Hprefix.
  rewrite (take_drop_commute (take prefix before ++ suffix) count start).
  rewrite (take_app_le (take prefix before) suffix (start + count)
    ltac:(rewrite (length_take_le before prefix Hprefix); exact Hwindow)).
  rewrite take_take.
  rewrite (Nat.min_l (start + count) prefix Hwindow).
  rewrite <- (take_drop_commute before count start).
  reflexivity.
Qed.

Ltac zesu_list_window_bounds :=
  repeat first
    [ progress (rewrite length_take)
    | progress (rewrite length_drop)
    | progress (rewrite List.app_length) ];
  repeat match goal with
  | Hlength : List.length ?bytes = ?count |- context [List.length ?bytes] =>
      is_closed_term count; progress (rewrite Hlength)
  end;
  lia.

Ltac zesu_list_slice_windows :=
  first
    [ lazymatch goal with
      | |- context [take ?count (drop ?start (take ?prefix ?before ++ ?suffix))] =>
        progress (rewrite (zesu_take_drop_prefix before suffix prefix start count
          ltac:(zesu_list_window_bounds) ltac:(zesu_list_window_bounds)))
      end
    | lazymatch goal with
      | |- context [drop ?prefix (take ?prefix ?before ++ ?suffix)] =>
        progress (rewrite (drop_app_length' (take prefix before) suffix prefix
          ltac:(rewrite (length_take_le before prefix ltac:(zesu_list_window_bounds)); reflexivity)))
      end
    | multimatch goal with
      | |- context [take ?count ?tail] =>
        progress (rewrite (take_ge tail count ltac:(zesu_list_window_bounds)))
      end ].
