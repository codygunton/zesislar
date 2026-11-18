Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.EntryWitnessProfile.
Require Import ZesuSsz.Evidence.EntryWitnessSelector.
Require Import ZesuSsz.Generated.DecodeItem.EntryWitnessData329.
Require Import ZesuSsz.Generated.DecodeItem.EntryWitnessData184.
From Coq Require Import Strings.String.
From lithium Require Import lvar interpreter base pure_definitions.
From iris.proofmode Require Import environments.
Open Scope string_scope.
Definition profile_value136 := ZesuWitnessProfileSlot "value" Z ZesuWitnessProfileEnd.
#[local] Instance source_value136 : ZesuEntryWitnessSourceProfile tt (Z * unit) :=
 {| zesu_source_profile_declaration := "1abf5b9b0c42569aa0bd6f020bf980de8cd609c28edf4d9885d7aff33d85022d";
    zesu_source_profile_slots := profile_value136 |}.
#[local] Instance data_value136 : ZesuEntryWitnessDataProfile tt (Z * unit) :=
 {| zesu_data_profile_declaration := "1abf5b9b0c42569aa0bd6f020bf980de8cd609c28edf4d9885d7aff33d85022d";
    zesu_data_profile_mapping := "da3a9a51bb192a1a7d98f6739d369aa19dd26fbcdeef88979621cd8af51e6545";
    zesu_data_profile_slots := profile_value136 |}.

Lemma metadata_reversal136 : True.
Proof.
 zesu_entry_witness_profile_check profile_value136 profile_value136
   constr:((Z * unit)%type) constr:(li_prod Z unit).
 exact I.
Qed.

Lemma metadata_same_type_name_swap_refuses136 : True.
Proof.
 Fail let expected := constr:(ZesuWitnessProfileSlot "n" Z (ZesuWitnessProfileSlot "i" Z ZesuWitnessProfileEnd)) in
 let swapped := constr:(ZesuWitnessProfileSlot "i" Z (ZesuWitnessProfileSlot "n" Z ZesuWitnessProfileEnd)) in
 zesu_entry_witness_profile_check expected swapped
   constr:((Z * (Z * unit))%type) constr:(li_prod Z (li_prod Z unit)).
 exact I.
Qed.

Lemma metadata_target_type_refuses136 : True.
Proof.
 Fail zesu_entry_witness_profile_check profile_value136 profile_value136
   constr:((Z * unit)%type) constr:(li_prod (bv 64) unit).
 exact I.
Qed.

Lemma metadata_frozen_alias_accepts136 : True.
Proof.
 let profile := constr:(ZesuWitnessProfileSlot "n" (lvar "zesuLoopCount" Z)
   (ZesuWitnessProfileSlot "i" (lvar "zesuLoopIndex" Z)
   (ZesuWitnessProfileSlot "payloadStart" Z
   (ZesuWitnessProfileSlot "lengthBytes" (list (bv 8))
   (ZesuWitnessProfileSlot "loaded" (bv 64) ZesuWitnessProfileEnd))))) in
 zesu_entry_witness_profile_check profile profile
   constr:(Entry6a24RemainingWitnessType329)
   constr:(li_prod (bv 64) (li_prod (list (bv 8))
     (li_prod Z (li_prod (lvar "zesuLoopIndex" Z)
       (li_prod (lvar "zesuLoopCount" Z) unit))))).
 exact I.
Qed.

Lemma metadata_frozen_seven_alias_accepts136 : True.
Proof.
 let profile := constr:(ZesuWitnessProfileSlot "prefix" (bv 8)
   (ZesuWitnessProfileSlot "rest" (list (bv 8))
   (ZesuWitnessProfileSlot "n" (lvar "zesuLoopCount" Z)
   (ZesuWitnessProfileSlot "i" (lvar "zesuLoopIndex" Z)
   (ZesuWitnessProfileSlot "payloadStart" Z
   (ZesuWitnessProfileSlot "lengthBytes" (list (bv 8))
   (ZesuWitnessProfileSlot "loaded" (bv 64) ZesuWitnessProfileEnd))))))) in
 zesu_entry_witness_profile_check profile profile
   constr:(Entry6ac4WitnessType184)
   constr:(li_prod (bv 64) (li_prod (list (bv 8))
     (li_prod Z (li_prod (lvar "zesuLoopIndex" Z)
     (li_prod (lvar "zesuLoopCount" Z)
     (li_prod (list (bv 8)) (li_prod (bv 8) unit))))))).
 exact I.
Qed.

Lemma guard_then_unchanged_selector136 `{!islaG Sigma} `{!threadG} (K : iProp Sigma) :
 K ⊢ (∃ witness : li_prod Z unit, ⌜witness.1ₗ = 7%Z⌝ ∗ K)%I.
Proof.
 iIntros "HK".
 pose proof (@ZesuEntryWitnessPendingHere unit (Z * unit)%type tt (7%Z, tt)) as Hpending.
 lazymatch goal with
 | |- envs_entails _ (@bi_exist _ ?target_type ?body) =>
    zesu_entry_witness_ready constr:(tt) constr:((Z * unit)%type) target_type body
 end.
 zesu_entry_witness_consume.
 iSplit; [done | iFrame].
Qed.

Lemma premature_sixteen_refuses136 : True.
Proof.
 Fail let expected := constr:(ZesuWitnessProfileSlot "n" (lvar "zesuLoopCount" Z) (ZesuWitnessProfileSlot "i" (lvar "zesuLoopIndex" Z) (ZesuWitnessProfileSlot "payloadStart" (Z) (ZesuWitnessProfileSlot "lengthBytes" (list (bv 8)) (ZesuWitnessProfileSlot "loaded" (bv 64) (ZesuWitnessProfileEnd)))))) in
 zesu_entry_witness_profile_check expected expected
   constr:((lvar "zesuLoopCount" Z * (lvar "zesuLoopIndex" Z * (Z * (list (bv 8) * (bv 64 * unit)%type)%type)%type)%type)%type) constr:(li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
  (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
     (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
        (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
           (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
              (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                 (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                    (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                       (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                          (li_prod
                             (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                             (li_prod
                                (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                                (li_prod (list (bv (Npos (xO (xO (xO xH))))))
                                   (li_prod
                                      (list (bv (Npos (xO (xO (xO xH))))))
                                      (li_prod Z
                                         (li_prod
                                            (lvar
                                               (String
                                                 (Ascii.Ascii false true
                                                 false true true true true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false false true true false)
                                                 (String
                                                 (Ascii.Ascii true true false
                                                 false true true true false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false true true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 true true false false true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii true true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 false false true true true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true false
                                                 false true false false true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii false true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 true false false true true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false false true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 false true true true true
                                                 false) EmptyString)))))))))))))
                                               Z)
                                            (li_prod
                                               (lvar
                                                 (String
                                                 (Ascii.Ascii false true
                                                 false true true true true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false false true true false)
                                                 (String
                                                 (Ascii.Ascii true true false
                                                 false true true true false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false true true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 true true false false true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii true true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 false false true true true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true true false
                                                 false false false true false)
                                                 (String
                                                 (Ascii.Ascii true true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false true true true false)
                                                 (String
                                                 (Ascii.Ascii false true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 true false true true true
                                                 false) EmptyString)))))))))))))
                                                 Z) unit)))))))))))))))).
 exact I.
Qed.

Lemma premature_eighteen_refuses136 : True.
Proof.
 Fail let expected := constr:(ZesuWitnessProfileSlot "prefix" (bv 8) (ZesuWitnessProfileSlot "rest" (list (bv 8)) (ZesuWitnessProfileSlot "n" (lvar "zesuLoopCount" Z) (ZesuWitnessProfileSlot "i" (lvar "zesuLoopIndex" Z) (ZesuWitnessProfileSlot "payloadStart" (Z) (ZesuWitnessProfileSlot "lengthBytes" (list (bv 8)) (ZesuWitnessProfileSlot "loaded" (bv 64) (ZesuWitnessProfileEnd)))))))) in
 zesu_entry_witness_profile_check expected expected
   constr:((bv 8 * (list (bv 8) * (lvar "zesuLoopCount" Z * (lvar "zesuLoopIndex" Z * (Z * (list (bv 8) * (bv 64 * unit)%type)%type)%type)%type)%type)%type)%type) constr:(li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
  (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
     (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
        (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
           (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
              (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                 (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                    (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                       (li_prod (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                          (li_prod
                             (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                             (li_prod
                                (bv (Npos (xO (xO (xO (xO (xO (xO xH))))))))
                                (li_prod (list (bv (Npos (xO (xO (xO xH))))))
                                   (li_prod
                                      (list (bv (Npos (xO (xO (xO xH))))))
                                      (li_prod Z
                                         (li_prod
                                            (lvar
                                               (String
                                                 (Ascii.Ascii false true
                                                 false true true true true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false false true true false)
                                                 (String
                                                 (Ascii.Ascii true true false
                                                 false true true true false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false true true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 true true false false true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii true true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 false false true true true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true false
                                                 false true false false true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii false true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 true false false true true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false false true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 false true true true true
                                                 false) EmptyString)))))))))))))
                                               Z)
                                            (li_prod
                                               (lvar
                                                 (String
                                                 (Ascii.Ascii false true
                                                 false true true true true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false false true true false)
                                                 (String
                                                 (Ascii.Ascii true true false
                                                 false true true true false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false true true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 true true false false true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii true true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 false false true true true
                                                 false)
                                                 (String
                                                 (Ascii.Ascii true true false
                                                 false false false true false)
                                                 (String
                                                 (Ascii.Ascii true true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii true false true
                                                 false true true true false)
                                                 (String
                                                 (Ascii.Ascii false true true
                                                 true false true true false)
                                                 (String
                                                 (Ascii.Ascii false false
                                                 true false true true true
                                                 false) EmptyString)))))))))))))
                                                 Z)
                                               (li_prod
                                                 (list
                                                 (bv (Npos (xO (xO (xO xH))))))
                                                 (li_prod
                                                 (bv (Npos (xO (xO (xO xH)))))
                                                 unit)))))))))))))))))).
 exact I.
Qed.

#[local] Instance source_empty_declaration150 : ZesuEntryWitnessSourceProfile false (Z * unit) :=
 {| zesu_source_profile_declaration := "";
    zesu_source_profile_slots := profile_value136 |}.
#[local] Instance data_empty_declaration150 : ZesuEntryWitnessDataProfile false (Z * unit) :=
 {| zesu_data_profile_declaration := "";
    zesu_data_profile_mapping := "1111111111111111111111111111111111111111111111111111111111111111";
    zesu_data_profile_slots := profile_value136 |}.
#[local] Instance source_empty_mapping150 : ZesuEntryWitnessSourceProfile true (Z * unit) :=
 {| zesu_source_profile_declaration := "1111111111111111111111111111111111111111111111111111111111111111";
    zesu_source_profile_slots := profile_value136 |}.
#[local] Instance data_empty_mapping150 : ZesuEntryWitnessDataProfile true (Z * unit) :=
 {| zesu_data_profile_declaration := "1111111111111111111111111111111111111111111111111111111111111111";
    zesu_data_profile_mapping := "";
    zesu_data_profile_slots := profile_value136 |}.

Lemma empty_declaration_hash_refuses150 `{!islaG Sigma} `{!threadG} : True.
Proof.
 Fail let body := constr:(fun witness : li_prod Z unit => ((⌜True⌝)%I : iProp Sigma)) in
 zesu_entry_witness_ready constr:(false) constr:((Z * unit)%type) constr:(li_prod Z unit) body.
 exact I.
Qed.

Lemma empty_mapping_hash_refuses150 `{!islaG Sigma} `{!threadG} : True.
Proof.
 Fail let body := constr:(fun witness : li_prod Z unit => ((⌜True⌝)%I : iProp Sigma)) in
 zesu_entry_witness_ready constr:(true) constr:((Z * unit)%type) constr:(li_prod Z unit) body.
 exact I.
Qed.
