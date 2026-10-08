Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SwitchDispatch.
Set Default Proof Mode "Classic".

Definition byte_list_head_fact (values : list (bv 8)) (head : bv 8)
    (tail : list (bv 8)) : Prop := values = head :: tail.
Definition byte_list_cons_alias (head : bv 8) (tail : list (bv 8)) := head :: tail.
Global Typeclasses Opaque byte_list_head_fact byte_list_cons_alias.

Lemma rule36_off (values : list (bv 8)) (head : bv 8) (tail : list (bv 8)) (Hhead : byte_list_head_fact values head tail) : (0 < length values)%nat.
Proof.
first [zesu_byte_list_containment_if_enabled; fail 1 "unexpected normalization success" | idtac]. unfold byte_list_head_fact in Hhead. rewrite Hhead. cbn [length]. lia.
Qed.
