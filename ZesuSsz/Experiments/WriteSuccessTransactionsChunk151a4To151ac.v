From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderU256.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1519c.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Remove Hints find_body_a151a4_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_151a4_to_151ac
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x151ac (writeSuccessTransactionsAt151acSpec P) -∗
  instr_body 0x151a4 (writeSuccessTransactionsAt151a4Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: repeat iIntros "?".
  all: lazymatch goal with
    | |- environments.envs_entails _ _ =>
        iDestruct select (base ↦ₘ∗ prefix ∗ _)%I as
          "(HbasePrefix & HbaseSuffix & Hprocessed & Htransaction & Hremaining &
            Hmmio & Htrace & HP & #Hinvariant & Hexit & _)";
        iPoseProof "Hinvariant" as "#HinvCopy";
        iEval
          (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
          in "HinvCopy";
        iDestruct "HinvCopy" as
          "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & %Hmax & _)";
        have Hsp128 : bv_unsigned (sp + 128) = bv_unsigned sp + 128 by
          (rewrite bv_add_unsigned bv_unsigned_BV;
           apply bv_wrap_small;
           pose proof (bv_unsigned_in_range 64 sp);
           pose proof (bv_unsigned_in_range 64 (BV 64 128));
           unfold bv_modulus in *; cbn in *; lia);
        have Hextract128 : bv_extract 0 3 (sp + 128) = 0%bv by
          bv_solve;
        li_unfold_lets_in_context; simpl; try liToSyntaxGoal;
        unfold TRACE_LET, LET_ID in *; unLET;
        lazymatch goal with
        | |- context [FindMemMapsTo (bv_unsigned ?address)] =>
            assert (bv_unsigned address = (bv_unsigned sp + 128)%Z) as Haddress
              by (change (bv_unsigned (sp + 128) = bv_unsigned sp + 128);
                  exact Hsp128);
            rewrite Haddress
        end;
        liARun
    | _ => try done
    end.
  Unshelve.
  all: try prepare_sidecond.
  all: try liARun.
  Unshelve.
  all: lazymatch goal with
    | |- bv_extract 0 3 ?address = 0%bv =>
        change (bv_extract 0 3 address = 0%bv); exact Hextract128
    | |- 0x20000000 <= bv_unsigned ?address =>
        rewrite Hsp128; rewrite !bv_unsigned_BV; lia
    | |- bv_unsigned ?address <= 0x20000000 + 0x20000000 - 8 =>
        rewrite Hsp128; rewrite !bv_unsigned_BV; lia
    | _ => try done
    end.
  all: try liARun.
  all: try (lazymatch goal with
    | LET0 := _ |- _ => subst LET0
    end).
  all: iRename select (reg_col _)%I into "HotherFinal".
  all: iRename select ("x5" ↦ᵣ RVal_Bits _)%I into "H5Final".
  all: iRename select (bv_unsigned LET0 ↦ₘ _)%I into "H128Final".
  all: iAssert (("x5" ↦ᵣ: fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝))%I
    with "[H5Final]" as "H5Pred".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits b). iFrame. done. }
  all: iEval (rewrite !reg_col_cons reg_col_nil) in "HotherFinal".
  all: iDestruct "HotherFinal" as
    "(H1Final & H3Final & H4Final & H6Final & H7Final & H14Final &
      H15Final & H16Final & H17Final & H28Final & H29Final & H30Final &
      H31Final & _)".
  all: have H128Address : bv_unsigned LET0 = bv_unsigned sp + 128 by
    (change (bv_unsigned (sp + 128) = bv_unsigned sp + 128);
     exact Hsp128).
  all: iEval (rewrite H128Address) in "H128Final".
  all: iPoseProof "Hinvariant" as "#HinvariantFinal".
  all: iEval
    (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
    in "HinvariantFinal".
  all: iDestruct "HinvariantFinal" as
    "(%HtransactionsEq & %HbytesEq & %HprefixEq & %HsuffixEq &
      %HbytesAppend & %HbytesLength & %HprefixLength & %HsuffixLength &
      %HtransactionsBound & %HspAlign & %HspLower & %HspUpper &
      %HbaseAlign & %HbaseLower & %HbaseUpper & _)".
  all: rewrite /writeSuccessTransactionsAt151acSpec.
  all: iExists
    (tail, suffix, prefix, bytes, remaining, processed, transactions,
      transaction, base, sp, tt)ₗ.
  all: cbn.
  all: rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff
    /writeSuccessTransactionsMachine151ac.
  all: rewrite !reg_col_cons reg_col_nil.
  all: iFrame.
  all: done.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: done.
Qed.
