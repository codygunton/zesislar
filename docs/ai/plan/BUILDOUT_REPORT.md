# Builder buildout report

Status: draft at pushed root `7dfa8d5a` on 2026-09-26. Phase A and B1 are measured. B2 records seven stalled probes, and B3 records its stop. B4 has two selected rules. The endpoint preview at `264096af` passed both gates after the step-5 rulings. B5 remains open while current-root v2 arms and seven B2 probes remain pending.

## Phase A

The integration branch reached `1dedcaa2`. The 24-job root `check-iris` gate passed. It printed `uncached checks passed`, `exit 0`, and `0 Timeout!`. Its console records 23:15:01 to 23:52:30 on 2026-09-22. The batch peak was 99 GiB, and the guard reported no kills.

| Checkpoint | Gate time | Result |
|---|---:|---|
| A3, opt-in spec table | 2,269.5 s | Green at 24 jobs; peak 111 GiB. |
| A4, repaired v2 preview | 189.4 s | Green at 24 jobs; warm cache, peak 49 GiB. |
| A5, generator tools | 2,198.95 s | Green at 24 jobs. |
| A6 and guard integration | About 37 min 29 s | Green at 24 jobs; peak 99 GiB. |

The v1 benchmark after A6 changed zero outcomes, zero classes, and zero signatures against `ccf505e81f85` on all 305 lemmas and all 48 rule-15 lemmas. The external arms ran on pushed root `1dedcaa2`. The A6 gate compiled all proof changes.

The A6 list contains 198 lemmas in 160 modules. Its three comment lines explain the plan's earlier count of 201 lines. The four proof batches removed 1,296, 433, 217, and 26 hand lines, for 1,972 hand lines removed. Batch 2 changed 56 lemmas in 50 modules and removed 545 physical source lines. `Print Assumptions` stayed unchanged and closed for all four batches: 66/66, 56/56, 60/60, and 16/16 lemmas.

## B1: v2 rule measurements

The table records the collection worker's immutable `9ebff0c6` arms. Every rule changed zero closed outcomes on both frozen sets. The medians and class changes compare each arm with v1. A support import caused some apparent rule changes. The final B1 switch list appears below.

The external pre-B1 v2 arm on `1dedcaa2` changed 25 outcomes, 37 classes, and 39 signatures across 305 lemmas against v1. It changed 1 outcome, 4 classes, and 4 signatures across 48 rule-15 lemmas. These counts are a pre-B1 reference.

B1 merged as `b4761100`. That B1 set imports four switches: WitnessArith, SpecTail, LookupReduce, and SealedOpen. It excludes the zero-row CallReturn switch, which remains available as a separate opt-in arm. The standalone 24-job preview passed in about 40 minutes, with zero timeouts and a 103 GiB batch peak. Root `40cdc060` later added ExistentialArrayRestore and OutcomeHandoff to v2. The B4 table below measures those two additions against the B1 set.

The post-B1 v1 benchmark matched its frozen baseline on all 305 full-set rows and all 48 rule-15 rows. It changed zero outcomes, classes, signatures, and goal hashes in either set.

At later root `f425f7ea`, the current classifier changed nine `pred_class` values to C9 in the 305-row v1 set relative to frozen `1dedcaa2` v1. Outcomes, signatures, and goal hashes changed zero rows. The 48-row rule-15 set changed zero rows. These nine class changes are classifier output, not changes to the harness proof set.

The first 48-job benchmark arm-tree build exited 1 without a source error. The same tree passed a 24-job diagnostic gate. The resumed 305-lemma and 48-lemma probes then passed the v1 equality check.

| Arm | Full median Δ | Full class changes | Rule-15 median Δ | Rule-15 class changes | B1 status |
|---|---:|---|---:|---|---|
| spectable | +0.0 s | C1 −15; n/a +7; unknown +8 | −0.2 s | none | Measured; excluded from final v2 |
| wordarraybytes | +1.8 s | C2 −1; C1 +1 | −0.2 s | C2 −1; C1 +1 | Measured; excluded from final v2 |
| stackarray | +0.5 s | C1 −6; n/a +8; unknown −2 | +0.2 s | none | Measured; excluded; attribution ticket open |
| witnessarith | +0.8 s | C1 −6; n/a +8; unknown −2 | +1.0 s | none | Measured; included; attribution ticket open |
| spectail | +1.3 s | C1 −2; C3 +1; unknown +1 | −0.5 s | C1 −1; unknown +1 | Measured; included in final v2 |
| lookupreduce | +1.0 s | C3 −1; C6 +1 | +0.2 s | C3 −1; C6 +1 | Measured; included in final v2 |
| callreturn | +1.5 s | none | +0.2 s | none | Measured; excluded; remains opt-in |
| sealedopen | +4.8 s | C1 −14; C2 +1; C4 −3; n/a +21; unknown −5 | +2.0 s | none | Measured; included; attribution ticket open |
| v2 bundle | +4.3 s | C1 −28; C2 −17; C3 +1; C4 −4; n/a +45; unknown +3 | +2.4 s | C2 −1; unknown +1 | Superseded by the B1 final set |

The support-only `WriteSuccessExactPrefixStackFacts` arm moved C1 by −7. The `InterfacesCoverage` support-only arm moved C1 by −14. Those controls prevent attribution of these changes to stackarray, witnessarith, or sealedopen. The attribution tickets remain open; the arm measurements are complete. The v2 bundle also caused 45 probes to stop compiling, so class movement alone is not a proof result.

The independent final post-B1 v2 arm compared `b4761100032b-v2*.json` with `1dedcaa280d2-v2*.json`. Across 305 full-set rows, both arms had 279 residual, two closed, and 24 errors. The median changed from 7.26 s to 7.01 s. Across 48 rule-15 rows, both arms had 46 residual and two closed; the median changed from 7.26 s to 7.14 s. No outcome changed. The only class change in each set was suffix entry C3→C6: `find_in_context(FindStructRegMapsTo)` became `∗[2] ↦ᵣ ∗ True`. Its goal hash changed from `c7299296dc1d5953ecf23afb815f5aa9038726803e229d5347511d5e7801d1fc` to `499d1178212c3814d174180209aed37a852720be96e1d6bceb0dbb8cb0b3deb8`.

The full set also had two signature-only changes in `WriteSuccessValueSuffix.v`: `write_success_value_suffix` and `write_success_value_suffix_pre` remained in the same class, but `find_in_context(FindStructRegMapsTo)` became `∗[2] ↦ₘ? ∗ True`. Both goal hashes changed from `acc9d78b4b84655b05b568d2cf141211f100cc719e6404d82141c9353ff623e1` to `b05d9e4e16160663bc086870d759f1db3c49e0fb5c6a2db25da485c0247a1a30`. Plan section 9 explains the 24 expected errors: v2 changes the search path in 20 modules that contain earlier hand proofs. New generated and direct segment modules import v2 alone; legacy hand-proof modules stay on v1.

## B2: seven segments

The seven B2 probes ran with the B1 switch set. They predate the two switches in root `40cdc060`. A5 probed suffix entry under an earlier v2 set in 4.4 s and found C3. That result does not replace its B2 row. No seven-segment probe set under the current v2 imports is recorded yet. The B2 harness patch `7f7ff3f9` passed check-fast. It selects the last `instr_body` entry, passes the private build directory to inference, and supplies the closed memcpy call premise. All seven patched probes remain pending.

| Segment | Range | Probe seconds | Outcome | Stall class and goal head | Inferred junction | Closed hand lines |
|---|---|---:|---|---|---|---:|
| Post-transactions | 0x15668→0x156e8 | 4.8 s | Stalled | C8: `∗[10] match ∗ ↦ₘ∗ ∗ (…)…`; goal head `match writeSuccessPostConditional1596c ... with ... end -∗ byteListItemResources ... ∗ ... -∗ ... -∗ zesu_ld_spec 87656 "x10" "x2" 1104` | Pending | N/A (open) |
| Post-withdrawals | 0x156e8→0x15744 | 2.4 s | Stalled | C6: `∃ : bv N *ₗ ()`; array sealed at 0x156e8 | Pending | N/A (open) |
| Suffix entry | 0x15744→0x15754 | 5.3 s | Stalled | C6: `∗[2] ↦ᵣ ∗ True`; goal head `encoderIntExactReturn ... -∗ "PC" ↦ᵣ ... -∗ WPasm ...` | Pending | N/A (open) |
| Tail fields 1 | 0x158e0→0x1596c | 7.0 s | Stalled | Unknown: `(encoderBytesExactReturn data size sp (Z_to_bv 64 (88300 + 4)) bytes b3 0 (Z_to_bv 64 (hashBase + length hashBytes)) word1 tail -∗ zesu_ld_spec 88304 "x10" "x2" 936) ∗ True` | Pending | N/A (open) |
| Tail fields 2 | 0x1596c→0x159b8 | 4.3 s | Stalled | C1: `∃ : spec *ₗ ()`; after one inferred event, 7.3 s at T2 return-to-load goal | One Boolean output event | N/A (open) |
| Tail fields 3 | 0x159b8→0x159d8 | 5.0 s | Stalled | C1: `∃ x : spec *ₗ list (bv 8) *ₗ (), ⌜encoderOptionalU64Valid (writeSuccessFrameSp witness + 296) x.2ₗ⌝ ∗` | Pending | N/A (open) |
| Epilogue | 0x159d8→0x15a0c | 5.8 s | Stalled | C4: `∃ x : isla_trace, Index.lookup (bv_unsigned ra) = Some x` | Pending | N/A (open) |

The suffix-entry C6 goal is the `encoderIntExactReturn` handoff at 0x15750. Its call premise at 0x15d10 uses `encoderIntEntryBoundary`, an alias of `zesuEncoderIntExactCallSpec`. The chain infers its only junction at 0x15744 and keeps the merged hashes-loop boundary at 0x15754 frozen.

A focused post-withdrawals probe on c4d44f8d rebuilt its dependencies in a private directory. With v2 and four closed call premises, it stalled in 3.3 s at frame 26 on C6, the existing `sp + 1136` load existential below. The outcome and goal head match the B2 row; this probe did not reach 0x15744.

No B2 generated segment is closed or committed yet. The set of closed segments is empty, so no closed-segment hand-line count applies.

The final-v2 probe recorded these exact residual goal heads. Each block is the complete conclusion from the probe record.

<details><summary>Post-transactions: C8, 4.8 s</summary>

```coq
match WriteSuccessPostTransactionDescriptors.writeSuccessPostConditional1596c (writeSuccessPostData witness) with
  | Some value =>
      match WriteSuccessPostTransactionDescriptors.writeSuccessPostConditional1596cPayload (writeSuccessPostData witness) with
      | Some payload => WriteSuccessPostTransactionResources.writeSuccessDescriptorResources value payload
      | None => False
      end
  | None => match WriteSuccessPostTransactionDescriptors.writeSuccessPostConditional1596cPayload (writeSuccessPostData witness) with
            | Some _ => False
            | None => True
            end
  end -∗
  (fix byteListItemResources (Sigma0 : gFunctors) (islaG1 : islaG Sigma0) (address : Z) (items : list ByteListItem) {struct items} : iProp Sigma0 :=
     match items with
     | [] => True
     | item :: rest => address ↦ₘ byteListData item ∗ (address + 8) ↦ₘ byteListSize item ∗ bv_unsigned (byteListData item) ↦ₘ∗ byteListBytes item ∗
         ⌜bv_unsigned (byteListSize item) = length (byteListBytes item)⌝ ∗ byteListItemResources Sigma0 islaG1 (address + 16) rest
     end) Sigma islaG0 (bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 14))
    (WriteSuccessPostTransactionDescriptors.writeSuccessPostByteLists159c8 (writeSuccessPostData witness)) ∗
  ⌜WriteSuccessPostTransactionResources.writeSuccessPostTransactionDataFacts (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness)
     (writeSuccessPostData witness)⌝ -∗
  writeSuccessNativeStaticResources ∗
  writeSuccessTransactionsInvariant (writeSuccessFrameSp witness) (writeSuccessTransactionBase witness) (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
    (writeSuccessTransactionBytes witness) [] (writeSuccessTransactionBytes witness) ∗ ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ P ∗ True -∗ True -∗ zesu_ld_spec 87656 "x10" "x2" 1104
```

</details>

<details><summary>Post-withdrawals: C6, 2.4 s</summary>

```coq
∃ y : bv 64 *ₗ (), (bv_unsigned (writeSuccessFrameSp witness) + 1136) ↦ₘ y.1ₗ ∗ ⌜bv_unsigned (writeSuccessFrameSp witness) `mod` 8 = 0⌝ ∗
    ⌜0 ≤ bv_unsigned (writeSuccessFrameSp witness) + 1136 < 0 + 1073741824⌝ ∗
    instr_pre (87784 + 4) (reg_col zesu_ram_sys_regs ∗ "x10" ↦ᵣ RVal_Bits y.1ₗ ∗ "x2" ↦ᵣ RVal_Bits (writeSuccessFrameSp witness) ∗ (bv_unsigned (writeSuccessFrameSp witness) + 1136) ↦ₘ y.1ₗ ∗ True)
```

</details>

<details><summary>Suffix entry: C6, 5.3 s</summary>

```coq
(encoderIntExactReturn sp (Z_to_bv 64 (87884 + 4)) (writeOutputEventsAny (sp + 1744) 32 (writeSuccessHashesEvents sp remaining tail)) -∗
   "PC" ↦ᵣ RVal_Bits (Z_to_bv 64 (87884 + 4)) -∗
   WPasm
     (Smt (DeclareConst 2 (Ty_BitVec 64)) Mk_annot :t:
      Assume
        (AExp_Binop Eq (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot; AExp_Val (AVal_Bits 131072%bv) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits 0%bv) Mk_annot)
           Mk_annot) Mk_annot :t:
      Smt (DeclareConst 3 (Ty_BitVec 64)) Mk_annot :t:
      Assume (AExp_Binop Eq (AExp_Unop (Extract 1 0) (AExp_Val (AVal_Var "PC" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits 0%bv) Mk_annot) Mk_annot) Mk_annot :t:
      ReadReg "PC" [] (RVal_Symbolic 3) Mk_annot :t:
      Smt (DefineConst 4 (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 3) Mk_annot; Val (Val_Bits 4%bv) Mk_annot] Mk_annot)) Mk_annot :t:
      Smt (DeclareConst 5 (Ty_BitVec 64)) Mk_annot :t:
      ReadReg "x8" [] (RVal_Symbolic 5) Mk_annot :t:
      Smt (DefineConst 6 (Binop Eq (Val (Val_Symbolic 5) Mk_annot) (Val (Val_Bits 0%bv) Mk_annot) Mk_annot)) Mk_annot :t:
      Smt (DefineConst 7 (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 3) Mk_annot; Val (Val_Bits 400%bv) Mk_annot] Mk_annot)) Mk_annot :t:
      tcases
        [Smt (Assert (Val (Val_Symbolic 6) Mk_annot)) Mk_annot :t:
         Smt (DefineConst 8 (Unop (Extract 0 0) (Binop (Bvarith Bvlshr) (Val (Val_Symbolic 7) Mk_annot) (Val (Val_Bits 1%bv) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
         BranchAddress (RVal_Symbolic 7) Mk_annot :t:
         WriteReg "PC" [] (RVal_Symbolic 7) Mk_annot :t:
         tnil; Smt (Assert (Unop Not (Val (Val_Symbolic 6) Mk_annot) Mk_annot)) Mk_annot :t:
               WriteReg "PC" [] (RVal_Symbolic 4) Mk_annot :t:
               tnil])) ∗ True
```

</details>

<details><summary>Tail fields 1: unknown, 7.0 s</summary>

```coq
(encoderBytesExactReturn data size sp (Z_to_bv 64 (88300 + 4)) bytes b3 0 (Z_to_bv 64 (hashBase + length hashBytes)) word1 tail -∗ zesu_ld_spec 88304 "x10" "x2" 936) ∗ True
```

</details>

<details><summary>Tail fields 2: C1, 4.3 s</summary>

```coq
∃ x : spec *ₗ (), ⌜Snapshots.writeOutputEvents (writeSuccessEntrySp witness - (2000 + 9)) 1 (WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload 0) x.1ₗ ⊆ tail⌝ ∗
    ⌜bv_extract 0 4 (writeSuccessFrameSp witness) = 0%bv⌝ ∗ ⌜0 ≤ bv_unsigned (writeSuccessFrameSp witness) - 16⌝ ∗ ⌜bv_unsigned (writeSuccessFrameSp witness) < 0 + 1073741824⌝ ∗
    ⌜bv_extract 0 1 (Z_to_bv 64 (88476 + 4)) = 0%bv⌝ ∗ ⌜bv_extract 1 1 (Z_to_bv 64 (88476 + 4)) = 0%bv⌝ ∗ ⌜bv_extract 0 2 (Z_to_bv 64 (88476 + 4)) = 0%bv⌝ ∗
    instr_pre (bv_unsigned (Z_to_bv 64 (88476 + 4))) (encoderBooleanClosedReturn 0 (writeSuccessFrameSp witness) (Z_to_bv 64 (88476 + 4)) x.1ₗ) ∗ True
```

</details>

<details><summary>Tail fields 3: C1, 5.0 s</summary>

```coq
∃ x : spec *ₗ list (bv 8) *ₗ (), ⌜encoderOptionalU64Valid (writeSuccessFrameSp witness + 296) x.2ₗ⌝ ∗
    (⌜0 ≤ bv_unsigned (writeSuccessFrameSp witness + 296)⌝ ∗ ⌜bv_unsigned (writeSuccessFrameSp witness + 296) + length x.2ₗ < 0 + 1073741824⌝ ∗ mmio_range (604086456 + 8) 16 ∗
     spec_trace
       match encoderOptionalU64Outcome x.2ₗ with
       | Some value =>
           Snapshots.writeOutputEvents (writeSuccessEntrySp witness - (2000 + 25)) 1 (WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload 1)
             (Snapshots.writeOutputEvents (writeSuccessEntrySp witness - (2000 + 16)) 8
                [Z_to_bv 8 (bv_unsigned value `mod` 256); Z_to_bv 8 ((bv_unsigned value `div` 256) `mod` 256); Z_to_bv 8 (((bv_unsigned value `div` 256) `div` 256) `mod` 256);
                 Z_to_bv 8 ((((bv_unsigned value `div` 256) `div` 256) `div` 256) `mod` 256); Z_to_bv 8 (((((bv_unsigned value `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
                 Z_to_bv 8 ((((((bv_unsigned value `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
                 Z_to_bv 8 (((((((bv_unsigned value `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
                 Z_to_bv 8 ((((((((bv_unsigned value `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256)] x.1ₗ)
       | None => Snapshots.writeOutputEvents (writeSuccessEntrySp witness - (2000 + 9)) 1 (WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload 0) x.1ₗ
       end ∗ ⌜bv_extract 0 4 (writeSuccessFrameSp witness) = 0%bv⌝ ∗ ⌜0 ≤ bv_unsigned (writeSuccessFrameSp witness) - 32⌝ ∗ ⌜bv_unsigned (writeSuccessFrameSp witness) < 0 + 1073741824⌝ ∗
     ⌜bv_extract 0 1 (Z_to_bv 64 (88504 + 4)) = 0%bv⌝ ∗ ⌜bv_extract 1 1 (Z_to_bv 64 (88504 + 4)) = 0%bv⌝ ∗ ⌜bv_extract 0 2 (Z_to_bv 64 (88504 + 4)) = 0%bv⌝ ∗
     instr_pre (bv_unsigned (Z_to_bv 64 (88504 + 4)))
       (encoderOptionalU64ExactReturn (writeSuccessFrameSp witness + 296) (writeSuccessFrameSp witness) (Z_to_bv 64 (88504 + 4)) old_x8 x.2ₗ x.1ₗ (encoderOptionalU64Outcome x.2ₗ)) ∗ True) ∗
    ⌜x.2ₗ =
     [Z_to_bv 8
        (Z.land (bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 10))
           (Z.ones 8));
      Z_to_bv 8
        (Z.land (bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 10) ≫ 8)
           (Z.ones 8));
      Z_to_bv 8
        (Z.land
           ((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 10) ≫ 8) ≫ 8)
           (Z.ones 8));
      Z_to_bv 8
        (Z.land
           (((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 10) ≫ 8) ≫ 8)
            ≫ 8) (Z.ones 8));
      Z_to_bv 8
        (Z.land
           ((((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 10) ≫ 8) ≫ 8)
             ≫ 8) ≫ 8) (Z.ones 8));
      Z_to_bv 8
        (Z.land
           (((((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 10) ≫ 8) ≫ 8)
              ≫ 8) ≫ 8) ≫ 8) (Z.ones 8));
      Z_to_bv 8
        (Z.land
           ((((((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 10) ≫ 8)
                ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8));
      Z_to_bv 8
        (Z.land
           (((((((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 10) ≫ 8)
                 ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8));
      Z_to_bv 8
        (Z.land (bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 11))
           (Z.ones 8));
      Z_to_bv 8
        (Z.land (bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 11) ≫ 8)
           (Z.ones 8));
      Z_to_bv 8
        (Z.land
           ((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 11) ≫ 8) ≫ 8)
           (Z.ones 8));
      Z_to_bv 8
        (Z.land
           (((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 11) ≫ 8) ≫ 8)
            ≫ 8) (Z.ones 8));
      Z_to_bv 8
        (Z.land
           ((((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 11) ≫ 8) ≫ 8)
             ≫ 8) ≫ 8) (Z.ones 8));
      Z_to_bv 8
        (Z.land
           (((((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 11) ≫ 8) ≫ 8)
              ≫ 8) ≫ 8) ≫ 8) (Z.ones 8));
      Z_to_bv 8
        (Z.land
           ((((((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 11) ≫ 8)
                ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8));
      Z_to_bv 8
        (Z.land
           (((((((bv_unsigned (WriteSuccessPostTransactionResources.writeSuccessPostWord (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 11) ≫ 8)
                 ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8))]⌝
```

</details>

<details><summary>Epilogue: C4, 5.8 s</summary>

```coq
∃ x : isla_trace, Index.lookup (bv_unsigned ra) = Some x
```

</details>

The post-withdrawals control omitted the closed spec table. It kept the array visible and stalled in 40.1 s at C1 with frame 96. Its exact goal follows.

<details><summary>Post-withdrawals control: C1, 40.1 s</summary>

```coq
∃ x : spec *ₗ (),
    ⌜Snapshots.writeOutputEvents (writeSuccessEntrySp witness - (2000 + 16)) 8
       [Z_to_bv 8 (bv_unsigned vmem `mod` 256); Z_to_bv 8 ((bv_unsigned vmem `div` 256) `mod` 256); Z_to_bv 8 (((bv_unsigned vmem `div` 256) `div` 256) `mod` 256);
        Z_to_bv 8 ((((bv_unsigned vmem `div` 256) `div` 256) `div` 256) `mod` 256); Z_to_bv 8 (((((bv_unsigned vmem `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
        Z_to_bv 8 ((((((bv_unsigned vmem `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
        Z_to_bv 8 (((((((bv_unsigned vmem `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
        Z_to_bv 8 ((((((((bv_unsigned vmem `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256)] x.1ₗ ⊆ writeSuccessExactPostWithdrawalsEvents witness⌝ ∗
    ⌜bv_unsigned (writeSuccessFrameSp witness) `mod` 16 = 0⌝ ∗ ⌜0 ≤ bv_unsigned (writeSuccessFrameSp witness) - 16⌝ ∗ ⌜bv_unsigned (writeSuccessFrameSp witness) < 0 + 1073741824⌝ ∗
    ⌜bv_extract 0 1 (Z_to_bv 64 87792 + 4) = 0%bv⌝ ∗ ⌜bv_extract 1 1 (Z_to_bv 64 87792 + 4) = 0%bv⌝ ∗ ⌜bv_extract 0 2 (Z_to_bv 64 87792 + 4) = 0%bv⌝ ∗
    instr_pre (bv_unsigned (Z_to_bv 64 87792 + 4)) (WriteSuccessExactEncoderIntCall.encoderIntExactReturn (writeSuccessFrameSp witness) (Z_to_bv 64 87792 + 4) x.1ₗ) ∗ True
```

</details>

After one inferred Boolean output event, tail fields 2 stalled in 7.3 s at the T2 goal:

```coq
(encoderBooleanClosedReturn 0 (writeSuccessFrameSp witness) (Z_to_bv 64 (88476 + 4)) tail -∗ zesu_ld_spec 88480 "x8" "x2" 96) ∗ True
```

## B3 and B4

Post-withdrawals B3 inference omitted the closed spec table and found one output event. It reached zero junctions. Thus, chain generation had no starting junction and B3 stopped. Round 2 stopped in 46.3 s at frame 97, class C1, on the loaded-word trace inclusion. These measurements predate root `40cdc060`. The exact round-2 goal follows.

A focused B3 retry with v2 and the four closed call premises stopped in 3.8 s at frame 27 on the same C6 `sp + 1136` load. Round 0 inferred zero events. It reached no junction, so `chain.py` had no starting junction.

<details><summary>Post-withdrawals B3 round 2: C1, frame 97</summary>

```coq
∃ x : spec *ₗ (),
    ⌜scons_snap (SWriteMem (BV 64 (604086456 + 16)) 8%bv)
       (λ snapshot : seq_snapshot,
          read_mem_list (snap_mem snapshot) (bv_unsigned (writeSuccessEntrySp witness - (2000 + 16))) 8 =
          Some
            [Z_to_bv 8 (bv_unsigned vmem `mod` 256); Z_to_bv 8 ((bv_unsigned vmem `div` 256) `mod` 256); Z_to_bv 8 (((bv_unsigned vmem `div` 256) `div` 256) `mod` 256);
             Z_to_bv 8 ((((bv_unsigned vmem `div` 256) `div` 256) `div` 256) `mod` 256); Z_to_bv 8 (((((bv_unsigned vmem `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
             Z_to_bv 8 ((((((bv_unsigned vmem `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
             Z_to_bv 8 (((((((bv_unsigned vmem `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
             Z_to_bv 8 ((((((((bv_unsigned vmem `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256)]) x.1ₗ
     ⊆ scons_snap (SWriteMem (BV 64 (604086456 + 16)) 8%bv)
         (λ snapshot : seq_snapshot,
            read_mem_list (snap_mem snapshot) (bv_unsigned (writeSuccessEntrySp witness - (2000 + 16))) 8 =
            Some
              [Z_to_bv 8
                 (bv_unsigned
                    (default 0%bv (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8)))
                  `mod` 256);
               Z_to_bv 8
                 ((bv_unsigned
                     (default 0%bv (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8)))
                   `div` 256) `mod` 256);
               Z_to_bv 8
                 (((bv_unsigned
                      (default 0%bv
                         (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8)))
                    `div` 256) `div` 256) `mod` 256);
               Z_to_bv 8
                 ((((bv_unsigned
                       (default 0%bv
                          (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8)))
                     `div` 256) `div` 256) `div` 256) `mod` 256);
               Z_to_bv 8
                 (((((bv_unsigned
                        (default 0%bv
                           (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8)))
                      `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
               Z_to_bv 8
                 ((((((bv_unsigned
                         (default 0%bv
                            (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8)))
                       `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
               Z_to_bv 8
                 (((((((bv_unsigned
                          (default 0%bv
                             (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8)))
                        `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256);
               Z_to_bv 8
                 ((((((((bv_unsigned
                           (default 0%bv
                              (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8)))
                         `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256)]) tail⌝ ∗ ⌜bv_unsigned (writeSuccessFrameSp witness) `mod` 16 = 0⌝ ∗
    ⌜0 ≤ bv_unsigned (writeSuccessFrameSp witness) - 16⌝ ∗ ⌜bv_unsigned (writeSuccessFrameSp witness) < 0 + 1073741824⌝ ∗ ⌜bv_extract 0 1 (Z_to_bv 64 87792 + 4) = 0%bv⌝ ∗
    ⌜bv_extract 1 1 (Z_to_bv 64 87792 + 4) = 0%bv⌝ ∗ ⌜bv_extract 0 2 (Z_to_bv 64 87792 + 4) = 0%bv⌝ ∗
    instr_pre (bv_unsigned (Z_to_bv 64 87792 + 4)) (WriteSuccessExactEncoderIntCall.encoderIntExactReturn (writeSuccessFrameSp witness) (Z_to_bv 64 87792 + 4) x.1ₗ) ∗ True
```

</details>

B3 found no junction at 0x15744 and could not start a chain. The present ticket list has five entries:

| Ticket | Goal head | Target segment |
|---|---|---|
| T1 | `∃ x : spec *ₗ (), ⌜scons_snap ... [vmem bytes] x.1ₗ ⊆ scons_snap ... [default lookup bytes] tail⌝ ∗` | Post-withdrawals |
| T2 | `(encoderBytesExactReturn ... -∗ zesu_ld_spec 88304 "x10" "x2" 936) ∗ True`; `(encoderBooleanClosedReturn ... -∗ zesu_ld_spec 88480 "x8" "x2" 96) ∗ True` | Tail fields 1 and 2 |
| T3 | `∃ y : bv 64 *ₗ (), (bv_unsigned (writeSuccessFrameSp witness) + 1136) ↦ₘ y.1ₗ ∗` | Post-withdrawals |
| T4 | `∃ x : spec *ₗ list (bv 8) *ₗ (), ⌜encoderOptionalU64Valid ... x.2ₗ⌝ ∗` | Tail fields 3 |
| T5 | `(R -∗ K) ∗ True`, for any continuation `K`; class C9 | Tail fields 1 and 2; 20 full-set and two rule-15 v2 rows |

These tickets come from `docs/ai/plan/DETERMINISM_TICKETS.md`. B2 and B3 may change their status after current-root probes. The residual goals above preserve the measured stop.

T5 generalizes the T2 return-to-load handoff. The existing call-return rule accepts `WPasm`, but these continuations name resources or `zesu_ld_spec`. Opening the wand does not supply every load resource. Tail fields 1 must expose registers from `encoderBytesExactReturn`. Tail fields 2 must expose `x2` from `encoderBooleanClosedReturn` and the word at `sp + 96` from the caller frame. The estimates in `AUTOMATION_EVIDENCE.md` are not closed segment results. Current-root arms and segment probes must measure the candidate.

Post-withdrawals has the separate T3→T1 gap. T3 must supply element 13 of `(sp + 1032) ↦ₘ∗ take 69 values` to the load at `sp + 1136`. T1 then relates each loaded word to its lookup for the output-trace inclusion. A chain-end equivalence lemma must expose the declared trace. Existing inference declares both writes, but that round exceeds 300 seconds. The evidence requires a split at the call at `0x156fc` before another probe. No complete post-withdrawals segment or junction is recorded.

The T2-a opt-in arm is rejected for merge. Across 305 full-set rows, two closed outcomes stayed closed, seven new errors appeared, and 17 classes changed. Across 48 rule-15 rows, two closed outcomes stayed closed, no new error appeared, and one timeout became a residual. The exact carrier probe failed at `WriteSuccessNativeSuffixBytes158e0Carrier__write_success_suffix_bytes_158f0_carrier.v:155`: `iExists` expected an existential, but the rule yielded a wand frame.

The fixed-harness v2 reruns for T1-b and T2-a each import `Sets.v2` plus the candidate switch. Against frozen `1dedcaa2` v2, both 305-row arms had 279 residual, two closed, and 24 expected hand-module errors. Each changed zero outcomes, one class (suffix entry C3→C6), and three full-set signatures and goal hashes. Their 48-row arms each had 46 residual and two closed; each changed zero outcomes, one class, and one signature and goal hash. The class and signature moves were already present in the post-B1 v2 arm, so neither candidate added a new proof outcome.

The T2-b fixed-harness v2 arms used commit `c4d44f8d` and its opt-in switch. The 305-row arm had 279 residual, two closed, and 24 expected hand-module errors; its median was 6.3 s. The 48-row arm had 46 residual and two closed; its median was 5.0 s. Against frozen `1dedcaa2` v2, both arms changed zero outcomes. The full set had the suffix-entry C3→C6 move and three signature and goal-hash changes; the 48-row set had the suffix-entry class, signature, and hash change. These changes match the post-B1 baseline, so T2-b added no candidate-specific residual movement.

The external `c4d44f8d` baseline arms completed in the determinism worktree. V1 had 302 residual, two closed, and one timeout on 305 rows (median 11.02 s); its rule-15 set had 45 residual, two closed, and one timeout on 48 rows (median 9.77 s). V2 had 279 residual, two closed, and 24 errors on 305 rows (median 7.01 s); its rule-15 set had 46 residual and two closed on 48 rows (median 7.77 s). From v1 to v2, 24 full-set residuals became errors and the epilogue timeout became a residual. The rule-15 outcome change was only that timeout-to-residual move. No closed outcome changed. The full set changed 37 classes and signatures and 63 goal hashes; rule-15 changed four of each. These counts come from the four `c4d44f8da061*.json` arm records.

The switched T3-a fixed-harness v2 arms used commit `4399fd2d`. The 305-row arm had 279 residual, two closed, and 24 expected hand-module errors; its median was 5.3 s. The 48-row arm had 46 residual and two closed; its median was 5.1 s. Against frozen `1dedcaa2` v2, both arms changed zero outcomes. The full set had the suffix-entry C3→C6 move and three signature and goal-hash changes; the 48-row set had the suffix-entry class, signature, and hash change. These changes match the post-B1 baseline, so T3-a added no candidate-specific corpus movement.

Neither frozen benchmark set contains `PostWithdrawalsSegment`, `TailFieldsFirstSegment`, or `TailFieldsSecondSegment`. T3-a's local post-withdrawals C6→C1 result and T2-b's local tail-fields results are separate evidence. T2-b landed in root `c4d44f8d` as an opt-in rule. The lead parked T3-a, T1-a, T1-b, and T2-a after the final arms. The selected B4 rules are in the table below.

The first T1-b arm is invalid. All 305 probes returned setup errors because the benchmark ran each probe from the caller's working directory. A relative `_build/default` recipe in the immutable arm tree then resolved against the wrong tree. The harness repair sets the subprocess working directory to that immutable tree for each probe. The corrected 305-row arm reported two closed, 303 residual, and no errors. It moved one timeout to a residual and changed two classes. The corrected 48-row rule-15 arm reported two closed, 46 residual, and no errors. It also moved one timeout to a residual and changed two classes. The harness repair passed check-fast and was pushed as `e7c72033`. Its first standalone tools-only 24-job preview on `b4761100` plus `e7c72033` failed after 24 minutes: `WriteSuccessExactTransactionsOptionPrefix.v:46` emitted `Fatal error: out of memory`. That preview had zero timeouts and a 100 GiB peak. The same module passed isolated scratch in 100.837 seconds with 1.68 GiB RSS. The isolated 24-job full rerun passed in 23 minutes with a 43 GiB peak. The fixed harness was merged and pushed at root `f425f7ea`.

T1-b is rejected for B4 because its post-withdrawals no-table C1 residual was byte-for-byte unchanged. The baseline probe took 43.1 s, and the T1-b probe took 42.3 s; both stopped at frame 96. T1-a's exact PW wrapper test rewrote eight loaded-word terms in 0.002 s and closed with an explicit trace witness. The real PW round-2 probe advanced past the loaded-word inclusion: the baseline took 46.3 s and stopped at C1, frame 97, with eight `default` terms in its goal (SHA256 `a4c4e31b3bd6519aacd77e08da6b865919cc15722fd294652b1393dd0543675e`). With T1-a, it took 81.4 s and stopped at the next output event and PC 87808, C1, frame 116, with no `default` term in its goal (SHA256 `405844f0674a36c4de5602dd7d53254c6f4a8fd60417da483f2a1d687e3dff79`). The new context has `Hlookup0` for the next word at `sp + 1144`. Static round-3 inference replaces `vmem0` with that lookup's `default` value, so its next event contains eight new `default` terms. This supplies a second syntactic site for B4's two-site rule. A paired round-3 probe ran beside an independent 42-job build. Its control stalled at C1, frame 97, in 184.3 s; the candidate reached the 300 s wall limit without a residual. The candidate input has 16 `default` terms rather than eight, and its generated source is only 2,173 bytes larger. The rule removes a matching `default` on each successful rewrite, so this record does not show a local rewrite loop. Those shared-load times cannot select a rule. The exact second-site wrapper closed under isolated focused compilation in 1.040 s; `zesu_rule_set_v2_steps` took 0.002 s, and `Print Assumptions` was closed under the global context. The full two-site segment remains untested and open.

Both T3 candidates advanced post-withdrawals from C6 to C1 at frame 92. T3-a took 46.4 s; T3-b took 40.8 s. The lead parked both candidates. T2-b branch `d4e7e62b` passed focused tests and check-fast. Its standalone full preview passed at 24 jobs in 42 minutes, with zero timeouts and a 115 GiB batch peak. Its serial guarded probes advanced tail fields 1 in 12.2 s to C6 frame 38, an existential for the `x2 + 936` load and `instr_pre 88308`. Tail fields 2 advanced in 14.2 s to C6 frame 36, the same shape for the `x2 + 96` load and `instr_pre 88484`.

T4-b's guarded witness selector passed its focused test. The exact tail-fields-3 probe selected the witness, then stopped because `iEval` could not rewrite inside the sealed `spec_trace`. The lead parked T4-b. T4-a's synthetic tests passed. Its exact tail-fields-3 `zesu_run` advanced beyond C1, so the former line-35 `iIntro` step became stale. Neither T4 candidate has a closed segment result yet.

## B4: selected arms at root 40cdc060

The lead selected two opt-in rules after the final arms. `builder-unknown-row-1` at `6ccb7607` supplied ExistentialArrayRestore. `builder-t4-a` at `ce24f717` supplied OutcomeHandoff. Root `40cdc060` merged both into `Sets/v2.v` in one commit. The rejected candidate branches remain parked. The table compares each candidate arm with the final B1 v2 arm at `b4761100`, not with v1.

| Rule | 305-row outcome delta | 305-row median delta | 48-row outcome delta | 48-row median delta | Other changed row |
|---|---|---:|---|---:|---|
| ExistentialArrayRestore | Five residual→closed; closed 2→7 | −0.99 s | Four residual→closed; closed 2→6 | +0.25 s | Five carrier restorations; four belong to the 48-row set. |
| OutcomeHandoff | No outcome change; closed stays 2 | −1.25 s | No outcome change; closed stays 2 | +0.37 s | Tail fields 3 changes C1→unknown, with signature `spec`; it remains open. |

The candidate arm files are `6ccb7607d797-v2-ur1.json`, `6ccb7607d797-v2-ur1-rule15.json`, `ce24f717a9e0-v2-t4a.json`, and `ce24f717a9e0-v2-t4a-rule15.json` under `.worktrees/determinism/ZesuSsz/Evidence/residuals/benchmark/`. The comparison files are `b4761100032b-v2.json` and `b4761100032b-v2-rule15.json` in the same directory. The 305-row arms each retain 24 expected errors from legacy hand modules. No rule closes a whole B2 segment. OutcomeHandoff moves one measured row; the lead's step 4 selection supplies the ruling for this one-row rule.

The guarded v1 arm on `40cdc060` kept all 305 and 48 outcomes unchanged against `b4761100`. It reported two closed rows on each set. The 24-job `check-iris` preview passed with zero timeouts and a 94 GiB batch peak. The guard held the gate from 11:25:26 to 12:05:01 on 2026-09-25, a 39 min 35 s run. The log is `.worktrees/islaris-native/_build/agents/orch/logs/v2-keepers-preview-40cdc060.log`. The arm log is `v2-keepers-v1-arm-40cdc060.log` beside it. The gate time comes from `/run/user/1000/zesu-guard/guard.log`. The preceding Export fuel fix at `4d03f0eb` passed `check-fast`; its module took 4.079 s and 673 MiB in isolation.

## Plan section 14 step 5: compliance boundary

The lead parked three proposed `KnownBug` constructors for the withdrawal, transaction, and witness-header list-count limits. Their required computed paired mismatch tests were unavailable under the old endpoint projection and abstract `EvmSailAdapter` evaluators. No new constructor is accepted or merged.

Root `7dfa8d5a` now includes the endpoint, startup generation, proof split, B2 harness patch, reproduction record, and report updates. The merged batch passed check-fast in 0.534 seconds. Its full check-iris took 478.188 seconds at 24 jobs, with peak task RSS 2,234,872 KiB. The logs are `endpoint-batch-check-fast-0b128666.log` and `endpoint-batch-check-iris-0b128666.log` under `.worktrees/islaris-native/_build/agents/orch/logs/`. Current-root benchmark arms and all seven patched B2 probes remain pending.

The endpoint preview at `264096af` passed check-fast and the full check-iris gate. The full build took 2,245.399 seconds at 24 jobs. Its logs are `.worktrees/islaris-native/_build/agents/orch/logs/endpoint-check-fast-264096af.log` and `endpoint-check-iris-264096af.log` in that directory. The endpoint uses symbolic pinned ELF memory, host input memory, and a real output-event projection. Its statement keeps exactly the named `decodeOk` and `writeOk` proof premises. The pinned-code and non-vacuity lemmas are closed. `zesuCompliance` retains its existing `Admitted` status. CP4 still needs the whole-run adequacy bridge.

The user approved startup traces at `0x10120`, `0x10124`, and `0x10128`. The pinned binary, Islaris, generator, and single configuration remain unchanged. The generated outputs remain ignored files. Commit `aa86daed` records the commands and hashes in `experiments/islaris-startup/REPRODUCTION.md`. The base `PUSH3_PROGRESS.md` startup-approval entry records the same evidence.

Proof split `b754157a` preserves the public `transactions_source_authorization_restore_nonemptynonempty` statement. The public lemma and both resource helper lemmas print `Closed under the global context`. The isolated public module used 28.74 seconds CPU and 1,859,956 KiB RSS. The helper module used 3.91 seconds CPU and 686,396 KiB RSS. The split changes the proof structure and adds no endpoint premise.

## B5: report status and remaining evidence

| Required item | Current record | Pending work |
|---|---|---|
| v2 rule table and deltas | B1 table and the two B4 arms above; current v2 has six selected switches. | Run the plan section 15 current-root v2 arms on both frozen sets and record per-lemma diffs. |
| Seven segments | B2 table has seven timed stalls under the four-switch B1 set. | Run all seven patched probes under the current six-switch set; record any changed goal or outcome. Patch `7f7ff3f9` passed check-fast; no patched probe result is recorded. |
| First junction | B3 inferred one event and no junction; `chain.py` could not start. | Re-run only if the current-root post-withdrawals probe moves past its C6 load. |
| Cleanup lines | Phase A removed 1,972 hand lines across 198 lemmas in 160 modules. | None for the recorded Phase A batches. |
| Closed segment hand lines | No B2 generated segment closed. | Record hand lines and `Print Assumptions` for any later closed segment. |
| 24-job gate times | A3, A4, A5, A6, and B1 times appear above; T2-b took about 42 min; the `40cdc060` preview took 39 min 35 s; endpoint preview `264096af` took 2,245.399 s; the merged batch took 478.188 s, both at 24 jobs. | Record the gate for any later ordered merge. |
| Tickets | T1 loaded-word inclusion, T2 return-to-load, T3 `sp + 1136` memory, T4 optional outcome, and T5 generic return wand remain. | Measure T5 and the T3→T1 path on current-root probes. Keep the chain-end and split requirements explicit. |
| Compliance boundary | The lead parked three new `KnownBug` constructors. The approved endpoint preview passed both gates; startup trace approval and reproduction are recorded. | Close the whole-run adequacy bridge for CP4. Keep the parked constructors out of the merge. |

The current segment inputs are `ZesuSsz/Evidence/det/open_segments.json` and `ZesuSsz/Evidence/det/chain/post_withdrawals.json`. The recorded stalls are in `ZesuSsz/Evidence/det/wp4/stalls.jsonl`. The old draft report came from branch `builder-roota-pw` at `7ae0c1dc`. Branch `builder-report0` at `0be3adf6` holds earlier benchmark JSON. The draft branches `builder-seg-pw` (`b64d405d`), `builder-seg-tf1` (`3ced1187`), and `builder-seg-tf2` (`3dc4ddc0`) do not contain closed segment proofs. They stay parked for Phase C.

This report is a draft. Current-root v2 arms on both frozen sets and all seven B2 probes remain open, so the B5 stop and review have not occurred.
