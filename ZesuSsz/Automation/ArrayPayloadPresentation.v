Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Automation.Hooks.
From iris.proofmode Require Import environments.
Local Open Scope Z_scope.

(* The callback must prove the payload equality. Owners are never converted. *)
Ltac zesu_array_payload_from_spatial spatial sigma heap width address fraction bytes codec :=
  lazymatch spatial with
  | environments.Esnoc ?rest ?name ?available =>
      first [
        lazymatch available with
        | @mem_mapsto_array ?sourceSigma ?sourceHeap ?sourceWidth
            ?sourceAddress ?sourceFraction ?sourceBytes =>
            constr_eq sigma sourceSigma;
            constr_eq heap sourceHeap;
            constr_eq width sourceWidth;
            constr_eq fraction sourceFraction;
            assert_fails (has_evar sourceAddress);
            assert_fails (has_evar sourceBytes);
            let Haddress := fresh "HarrayAddressPresentation" in
            let Hbytes := fresh "HarrayPayloadPresentation" in
            assert (Haddress : sourceAddress = address) by reflexivity;
            assert (Hbytes : sourceBytes = bytes) by
              first [solve [codec] | solve [symmetry; codec]];
            try rewrite Haddress;
            rewrite Hbytes;
            clear Haddress Hbytes;
            iFrame;
            try (iPureIntro; repeat split;
                 ZesuSsz.Automation.MemoryAddress.zesu_stack_arithmetic)
        end
      | zesu_array_payload_from_spatial rest sigma heap width address fraction bytes codec]
  end.

Ltac zesu_array_payload_presentation codec :=
  lazymatch goal with
  | |- environments.envs_entails (environments.Envs _ ?spatial _) ?requested =>
      lazymatch requested with
      | context [@mem_mapsto_array ?sigma ?heap ?width ?address ?fraction ?bytes] =>
          assert_fails (has_evar address);
          assert_fails (has_evar fraction);
          assert_fails (has_evar bytes);
          zesu_array_payload_from_spatial spatial sigma heap width address fraction bytes codec
      end
  end.
