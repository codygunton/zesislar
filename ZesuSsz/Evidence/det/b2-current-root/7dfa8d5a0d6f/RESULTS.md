# Phase B2 probes at 7dfa8d5a

All seven probes used the approved contracts and rule set v2.
The guard limited the driver to two concurrent scratch compiles.
All seven probes stalled. No generated segment closed.
The four generated drafts use `.v.txt` files because their proofs remain unfinished.
Post-withdrawals remained at C6, so the conditional B3 chain did not run.

| Lemma | Seconds | Outcome | Class |
|---|---:|---|---|
| `write_success_exact_post_withdrawals_segment` | 3.9 | stalled | C6 |
| `write_success_exact_tail_fields_first_segment` | 9.2 | stalled | unknown |
| `write_success_exact_tail_fields_second_segment` | 6.1 | stalled | C1 |
| `write_success_exact_post_transactions_segment` | 5.6 | stalled | C8 |
| `write_success_exact_suffix_entry_segment` | 6.1 | stalled | C6 |
| `write_success_exact_tail_fields_third_segment` | 5.9 | stalled | unknown |
| `write_success_exact_epilogue_segment` | 7.9 | stalled | C4 |

## Exact residuals

### write_success_exact_post_withdrawals_segment

```coq
∃ y : bv 64 *ₗ (), (bv_unsigned (writeSuccessFrameSp witness) + 1136) ↦ₘ y.1ₗ ∗ ⌜bv_unsigned (writeSuccessFrameSp witness) `mod` 8 = 0⌝ ∗
    ⌜0 ≤ bv_unsigned (writeSuccessFrameSp witness) + 1136 < 0 + 1073741824⌝ ∗
    instr_pre (87784 + 4) (reg_col zesu_ram_sys_regs ∗ "x10" ↦ᵣ RVal_Bits y.1ₗ ∗ "x2" ↦ᵣ RVal_Bits (writeSuccessFrameSp witness) ∗ (bv_unsigned (writeSuccessFrameSp witness) + 1136) ↦ₘ y.1ₗ ∗ True)
```

### write_success_exact_tail_fields_first_segment

```coq
(encoderBytesExactReturn data size sp (Z_to_bv 64 (88300 + 4)) bytes b3 0 (Z_to_bv 64 (hashBase + length hashBytes)) word1 tail -∗ zesu_ld_spec 88304 "x10" "x2" 936) ∗ True
```

### write_success_exact_tail_fields_second_segment

```coq
∃ x : spec *ₗ (), ⌜Snapshots.writeOutputEvents (writeSuccessEntrySp witness - (2000 + 9)) 1 (WriteSuccessExactBooleanSpec.writeSuccessBooleanWordPayload 0) x.1ₗ ⊆ tail⌝ ∗
    ⌜bv_extract 0 4 (writeSuccessFrameSp witness) = 0%bv⌝ ∗ ⌜0 ≤ bv_unsigned (writeSuccessFrameSp witness) - 16⌝ ∗ ⌜bv_unsigned (writeSuccessFrameSp witness) < 0 + 1073741824⌝ ∗
    ⌜bv_extract 0 1 (Z_to_bv 64 (88476 + 4)) = 0%bv⌝ ∗ ⌜bv_extract 1 1 (Z_to_bv 64 (88476 + 4)) = 0%bv⌝ ∗ ⌜bv_extract 0 2 (Z_to_bv 64 (88476 + 4)) = 0%bv⌝ ∗
    instr_pre (bv_unsigned (Z_to_bv 64 (88476 + 4))) (encoderBooleanClosedReturn 0 (writeSuccessFrameSp witness) (Z_to_bv 64 (88476 + 4)) x.1ₗ) ∗ True
```

### write_success_exact_post_transactions_segment

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

### write_success_exact_suffix_entry_segment

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

### write_success_exact_tail_fields_third_segment

```coq
spec
```

### write_success_exact_epilogue_segment

```coq
∃ x : isla_trace, Index.lookup (bv_unsigned ra) = Some x
```
