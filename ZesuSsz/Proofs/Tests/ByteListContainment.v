Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SwitchDispatch.
Set Default Proof Mode "Classic".
Require Import ZesuSsz.Automation.Switches.ByteListContainment.

Definition byte_list_head_fact (values : list (bv 8)) (head : bv 8)
    (tail : list (bv 8)) : Prop := values = head :: tail.
Definition byte_list_cons_alias (head : bv 8) (tail : list (bv 8)) := head :: tail.
Global Typeclasses Opaque byte_list_head_fact byte_list_cons_alias.


Lemma rule36_folded_head (pointer : Z) (values : list (bv 8)) (head : bv 8) (tail : list (bv 8)) (Hhead : byte_list_head_fact values head tail) : (pointer <= pointer + 0 < pointer + Z.of_nat (length values) * Z.of_N (N.div 8 8))%Z.
Proof.
zesu_byte_list_containment_if_enabled. lia.
Qed.

Lemma rule36_reverse (values : list (bv 8)) (head : bv 8) (tail : list (bv 8)) (Hhead : head :: tail = values) : (0 < length values)%nat.
Proof.
zesu_byte_list_containment_if_enabled. lia.
Qed.

Lemma rule36_constructor_alias (values : list (bv 8)) (head : bv 8) (tail : list (bv 8)) (Hhead : values = byte_list_cons_alias head tail) : (0 < length values)%nat.
Proof.
zesu_byte_list_containment_if_enabled. lia.
Qed.

Lemma rule36_cached_on (values : list (bv 8)) (head : bv 8) (tail : list (bv 8)) (Hhead : byte_list_head_fact values head tail) : (0 < length values)%nat.
Proof.
assert (Hcache : ZesuSwitchDispatchCache [(ZesuStepByteListContainment, true)]) by constructor. zesu_byte_list_containment_if_enabled. lia.
Qed.

Lemma rule36_nil_rejected (values : list (bv 8)) (Hvalues : values = []) : length values = 0%nat.
Proof.
first [zesu_byte_list_containment_if_enabled; fail 1 "unexpected normalization success" | idtac]. rewrite Hvalues. reflexivity.
Qed.

Lemma rule36_nonmatching (values other : list (bv 8)) (head : bv 8) (tail : list (bv 8)) (Hhead : other = head :: tail) (Hlength : length values = 1%nat) : length values = 1%nat.
Proof.
first [zesu_byte_list_containment_if_enabled; fail 1 "unexpected normalization success" | idtac]. exact Hlength.
Qed.

Lemma rule36_cached_off (values : list (bv 8)) (head : bv 8) (tail : list (bv 8)) (Hhead : byte_list_head_fact values head tail) : (0 < length values)%nat.
Proof.
assert (Hcache : ZesuSwitchDispatchCache [(ZesuStepByteListContainment, false)]) by constructor. first [zesu_byte_list_containment_if_enabled; fail 1 "unexpected normalization success" | idtac]. unfold byte_list_head_fact in Hhead. rewrite Hhead. cbn [length]. lia.
Qed.

Lemma rule36_shared_evar_rollback  : True.
Proof.
evar (pending : list (bv 8)). assert (Haux : Coq.Init.Logic.True) by shelve. assert (Hprobe : length pending = length pending). 1: (first [zesu_byte_list_containment_if_enabled; fail 1 "unexpected normalization success" | idtac]). 1: (unfold pending; match goal with |- length ?values = _ => has_evar values; unify values (@nil (bv 8)) end; reflexivity). 1: exact I. Unshelve. all: exact I.
Qed.

Lemma rule36_self_rejected (values : list (bv 8)) (Hsame : values = values) : length values = length values.
Proof.
first [zesu_byte_list_containment_if_enabled; fail 1 "unexpected normalization success" | idtac]. reflexivity.
Qed.

Lemma rule36_unrelated_shared_evar (values : list (bv 8)) (head : bv 8) (tail : list (bv 8)) (Hhead : byte_list_head_fact values head tail) : True.
Proof.
evar (pending : nat). assert (Haux : Coq.Init.Logic.True) by shelve. assert (Hprobe : (0 < length values)%nat). 1: zesu_byte_list_containment_if_enabled. 1: (let value := eval unfold pending in pending in has_evar value; lia). 1: (let value := eval unfold pending in pending in has_evar value; unify value 0%nat; exact I). Unshelve. all: exact I.
Qed.

Lemma rule36_reverse_constructor_alias (values : list (bv 8)) (head : bv 8) (tail : list (bv 8)) (Hhead : byte_list_cons_alias head tail = values) : (0 < length values)%nat.
Proof.
zesu_byte_list_containment_if_enabled. lia.
Qed.
