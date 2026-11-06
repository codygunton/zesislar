Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith Bool.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation.ListHeadFromLength.
Import ListNotations.
Require Import ZesuSsz.Automation.All.
Open Scope Z_scope.

Lemma symbolic64 {A : Type} (bytes : list A) default quantity :
  quantity = Z.of_nat (length bytes) ->
  Z_to_bv 64 quantity <> BV 64 0 ->
  bytes = nth 0 bytes default :: skipn 1 bytes.
Proof. intros. zesu_list_head_from_length. Qed.

Lemma boolean16 (bytes : list nat) quantity :
  quantity = Z.of_nat (length bytes) ->
  negb (bool_decide (Z_to_bv 16 quantity = BV 16 0)) = true ->
  bytes = nth 0 bytes 0%nat :: skipn 1 bytes.
Proof. intros. zesu_list_head_from_length. Qed.

Goal forall (bytes : list nat) quantity,
  quantity = Z.of_nat (length bytes) ->
  bytes = nth 0 bytes 0%nat :: skipn 1 bytes.
Proof. intros. Fail solve [zesu_list_head_from_length]. Abort.

Goal forall (bytes : list nat) quantity,
  Z_to_bv 64 quantity <> BV 64 0 ->
  bytes = nth 0 bytes 0%nat :: skipn 1 bytes.
Proof. intros. Fail solve [zesu_list_head_from_length]. Abort.

Goal forall (bytes : list nat) quantity (zero : bv 64),
  quantity = Z.of_nat (length bytes) -> Z_to_bv 64 quantity <> zero ->
  bytes = nth 0 bytes 0%nat :: skipn 1 bytes.
Proof. intros. Fail solve [zesu_list_head_from_length]. Abort.

Goal forall (bytes other : list nat) quantity,
  quantity = Z.of_nat (length other) -> Z_to_bv 64 quantity <> BV 64 0 ->
  bytes = nth 0 bytes 0%nat :: skipn 1 bytes.
Proof. intros. Fail solve [zesu_list_head_from_length]. Abort.

Goal forall (bytes : list nat) quantity,
  quantity = Z.of_nat (length bytes) -> Z_to_bv 64 quantity <> BV 64 1 ->
  bytes = nth 0 bytes 0%nat :: skipn 1 bytes.
Proof. intros. Fail solve [zesu_list_head_from_length]. Abort.

Goal ([] : list nat) = nth 0 [] 0%nat :: skipn 1 [].
Proof. Fail solve [zesu_list_head_from_length]. Abort.
Print Assumptions symbolic64.
Print Assumptions boolean16.
