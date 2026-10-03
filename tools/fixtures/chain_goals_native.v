Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
Set Printing Width 200. Set Printing Depth 100000.
Ltac chain_print_environment marker environment :=
  lazymatch environment with
  | environments.Enil => idtac
  | environments.Esnoc ?rest ?name ?resource =>
      chain_print_environment marker rest;
      idtac marker resource "CHAIN-FIELD-END"
  end.
Ltac chain_print_goal phase :=
  idtac "CHAIN-GOAL-BEGIN" phase;
  try (multimatch goal with
    | Hlocal : ?T |- _ =>
      idtac "CHAIN-GOAL-LOCAL" Hlocal ":" T "CHAIN-FIELD-END";
      let S := type of T in
      idtac "CHAIN-GOAL-SORT" Hlocal ":" S "CHAIN-FIELD-END";
      try (lazymatch goal with
        | Hlocal := ?value : _ |- _ =>
          idtac "CHAIN-GOAL-VALUE" Hlocal ":" value "CHAIN-FIELD-END"
        end);
      fail
    end);
  lazymatch goal with
  | |- envs_entails ?environment ?conclusion =>
      idtac "CHAIN-GOAL-ENV" "iris" "CHAIN-FIELD-END";
      let persistent := eval cbv [environments.env_intuitionistic] in
        (environments.env_intuitionistic environment) in
      let spatial := eval cbv [environments.env_spatial] in
        (environments.env_spatial environment) in
      chain_print_environment "CHAIN-GOAL-PERSISTENT" persistent;
      chain_print_environment "CHAIN-GOAL-SPATIAL" spatial;
      idtac "CHAIN-GOAL-CONCLUSION" conclusion "CHAIN-FIELD-END"
  | |- ?conclusion =>
      idtac "CHAIN-GOAL-ENV" "coq" "CHAIN-FIELD-END";
      idtac "CHAIN-GOAL-CONCLUSION" conclusion "CHAIN-FIELD-END"
  end.

Lemma native_branches `{!islaG Sigma} `{!threadG} (sp : bv 64) (choice : bool) (tail : spec) :
 (0 <= bv_unsigned sp)%Z ->
 (if choice then (bv_unsigned sp ↦ₘ (BV 64 8) ∗ spec_trace (scons (SWriteMem (BV 64 604086464) (BV 64 8)) tail) ∗ mmio_range 604086464 16)%I
  else ((bv_unsigned sp + 8) ↦ₘ (BV 8 16) ∗ spec_trace (scons (SWriteMem (BV 64 604086464) (BV 8 16)) tail) ∗ mmio_range 604086464 16)%I) -∗ True%I.
Proof.
 intros Hbound. destruct choice; iIntros "(Howned & Htrace & #Hmmio)".
 all: assert (Hdebt : (0 <= bv_unsigned sp + 1)%Z) by shelve.
 all: try liShow.
Ltac chain_record_active := lazymatch goal with |- ?G => chain_print_goal "active"; try (iMatchHyp ltac:(fun H resource =>
  first [lazymatch resource with
    | @mem_mapsto _ _ ?width ?address _ _ =>
        try (lazymatch address with
          | context[@bv_unsigned ?addressWidth ?value] =>
            let addressWidth := eval vm_compute in addressWidth in
            idtac "BOUNDARY-ADDRESS-WIDTH" value ":" addressWidth
          end);
        let width := eval vm_compute in width in
        idtac "CHAIN-MEMORY-WIDTH" address ":" width
    end
  | lazymatch resource with
    | @mem_mapsto_array _ _ ?width ?address _ _ =>
        try (lazymatch address with
          | context[@bv_unsigned ?addressWidth ?value] =>
            let addressWidth := eval vm_compute in addressWidth in
            idtac "BOUNDARY-ADDRESS-WIDTH" value ":" addressWidth
          end);
        let width := eval vm_compute in width in
        idtac "CHAIN-MEMORY-WIDTH" address ":" width
    end
  | lazymatch resource with
    | spec_trace ?trace =>
        let rec events trace := lazymatch trace with
          | scons (SWriteMem ?address ?value) ?rest =>
              let width := eval vm_compute in (bvn_n value) in
              idtac "CHAIN-TRACE-WIDTH" address ":" width; events rest
          | scons_snap (SWriteMem ?address ?value) _ ?rest =>
              let width := eval vm_compute in (bvn_n value) in
              idtac "CHAIN-TRACE-WIDTH" address ":" width; events rest
          | _ => idtac
          end in events trace
    end]; fail)); idtac "CHAIN-GOAL-END" end.
all: chain_record_active.
 all: shelve.
 Unshelve.
 all: try liShow.
Ltac chain_record_shelved := lazymatch goal with |- ?G => chain_print_goal "shelved"; try (iMatchHyp ltac:(fun H resource =>
  first [lazymatch resource with
    | @mem_mapsto _ _ ?width ?address _ _ =>
        try (lazymatch address with
          | context[@bv_unsigned ?addressWidth ?value] =>
            let addressWidth := eval vm_compute in addressWidth in
            idtac "BOUNDARY-ADDRESS-WIDTH" value ":" addressWidth
          end);
        let width := eval vm_compute in width in
        idtac "CHAIN-MEMORY-WIDTH" address ":" width
    end
  | lazymatch resource with
    | @mem_mapsto_array _ _ ?width ?address _ _ =>
        try (lazymatch address with
          | context[@bv_unsigned ?addressWidth ?value] =>
            let addressWidth := eval vm_compute in addressWidth in
            idtac "BOUNDARY-ADDRESS-WIDTH" value ":" addressWidth
          end);
        let width := eval vm_compute in width in
        idtac "CHAIN-MEMORY-WIDTH" address ":" width
    end
  | lazymatch resource with
    | spec_trace ?trace =>
        let rec events trace := lazymatch trace with
          | scons (SWriteMem ?address ?value) ?rest =>
              let width := eval vm_compute in (bvn_n value) in
              idtac "CHAIN-TRACE-WIDTH" address ":" width; events rest
          | scons_snap (SWriteMem ?address ?value) _ ?rest =>
              let width := eval vm_compute in (bvn_n value) in
              idtac "CHAIN-TRACE-WIDTH" address ":" width; events rest
          | _ => idtac
          end in events trace
    end]; fail)); idtac "CHAIN-GOAL-END" end.
all: chain_record_shelved.
 all: first [lia | iPureIntro; exact I].
Qed.

From Coq Require Import Vectors.Vector.
Lemma native_dependent (n : nat) (values : Vector.t nat n) : True.
Proof.
 all: chain_record_active.
 exact I.
Qed.
