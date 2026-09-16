Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessRepresentation WriteSuccessEncodeFragments WriteSuccessObservation
  WriteSuccessOutputSemantic WriteSuccessOutputDescriptors.

Definition writeSuccessExactAuthorizationItemEvents (sp : bv 64)
    (bytes : list (bv 8)) (tail : spec) : spec :=
  let observation := writeSuccessAuthorizationObservationOfBytes bytes in
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
    (writeSuccessPrivateBytes (writeSuccessEncodeU256
      (observationAuthorizationChainId observation)))
    (writeOutputEvents (sp + BV 64 1856)%bv (BV 64 20)
      (writeSuccessPrivateBytes (observationAuthorizationAddress observation))
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64
          (observationAuthorizationNonce observation)))
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
          (writeSuccessPrivateBytes (writeSuccessEncodeU64
            (observationAuthorizationV observation)))
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
            (writeSuccessPrivateBytes (writeSuccessEncodeU256
              (observationAuthorizationR observation)))
            (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
              (writeSuccessPrivateBytes (writeSuccessEncodeU256
                (observationAuthorizationS observation))) tail))))).

Fixpoint writeSuccessExactAuthorizationEvents (sp : bv 64)
    (rows : list (list (bv 8))) (tail : spec) : spec :=
  match rows with
  | [] => tail
  | row :: rest => writeSuccessExactAuthorizationItemEvents sp row
      (writeSuccessExactAuthorizationEvents sp rest tail)
  end.

Lemma authorization_exact_events_descriptors sp rows tail :
  writeSuccessExactAuthorizationEvents sp rows tail =
  writeOutputPayloadsSpec (writeSuccessAuthorizationsDescriptors sp (length rows))
    (map writeSuccessPrivateBytes (concat (map
      (fun row => writeSuccessAuthorizationFragments
        (writeSuccessAuthorizationObservationOfBytes row)) rows))) tail.
Proof.
  induction rows as [|row rows IH]; first reflexivity.
  cbn [writeSuccessExactAuthorizationEvents writeSuccessAuthorizationsDescriptors
    map concat length].
  rewrite map_app. cbn [writeSuccessAuthorizationFragments map app].
  unfold writeSuccessExactAuthorizationItemEvents.
  rewrite IH. reflexivity.
Qed.
Print Assumptions authorization_exact_events_descriptors.
