(* Reuse an existential handoff's witnesses and restore its split byte array. *)

Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation.Hooks.
From iris.proofmode Require Import environments.

Class ZesuStepExistentialArrayRestore : Prop :=
  zesu_step_existential_array_restore : True.

Ltac zesu_restore_existential_array :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T _) =>
      iMatchHyp ltac:(fun H source =>
        let head := get_head source in
        let expanded := eval cbv beta delta [head] in source in
        lazymatch expanded with
        | @bi_exist _ _ _ =>
            iEval (unfold head) in H;
            repeat (iDestruct H as (?) H);
            iDestruct H as
              "(HkeptFirst & HsplitArray & HkeptThird & HkeptFourth & _)";
            let witness := zesu_tuple_witness T in
            iExists witness;
            iFrame "HkeptFirst HkeptThird HkeptFourth";
            iMatchHyp ltac:(fun Hsplit split =>
                let splitHead := get_head split in
                let splitBody := eval cbv beta delta [splitHead] in split in
                lazymatch splitBody with
                | @bi_exist _ (bv 8) _ =>
                    let byte := fresh "byte" in
                    iEval (unfold splitHead) in Hsplit;
                    iDestruct Hsplit as (byte)
                      "(Hprefix & Hbyte & Hsuffix & %Hlookup)";
                    iMatchHyp ltac:(fun Hprefix prefix =>
                      lazymatch prefix with
                      | (?address ↦ₘ∗ take ?index ?values)%I =>
                        iApply (mem_mapsto_array_recombine_u8_read
                          address values index byte
                          (address + Z.of_nat (S index))
                          (address + Z.of_nat index)
                          with "Hprefix Hsuffix Hbyte");
                        iPureIntro; first [assumption | reflexivity]
                      end)
                end)
        end)
  end.

Ltac zesu_restore_existential_array_if_enabled :=
  let _ := constr:(_ : ZesuStepExistentialArrayRestore) in
  zesu_restore_existential_array.
