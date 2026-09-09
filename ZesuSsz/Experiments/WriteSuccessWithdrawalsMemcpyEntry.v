From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.

Open Scope Z_scope.

Lemma writeSuccessMemcpyEntryShape destination source returnAddress bytes
    destinationBefore memoryFrame priorLog state :
  Inv_memcpy destination source returnAddress bytes destinationBefore
    memoryFrame priorLog state ->
  exists regs global,
    state.1 = writeSuccess101d4Before regs global.
Proof.
  intros Hinv.
  destruct state as [[[trace regs pcRegister nb] global] log].
  cbn in Hinv |- *.
  have Hboundary : IslaInstructionBoundary
      ({| seq_trace := trace; seq_regs := regs; seq_pc_reg := pcRegister;
          seq_nb_state := nb |}, global) by
    (unfold Inv_memcpy in Hinv; tauto).
  have HpcRegister : pcRegister = "PC" by
    (unfold Inv_memcpy in Hinv; tauto).
  subst pcRegister.
  have HconcretePc :
      match regs !! "PC" with
      | Some (RVal_Bits value) => Some (bvn_unsigned value)
      | _ => None
      end = Some 0x101d4 by
    (unfold Inv_memcpy, writeSuccessWithdrawalsConcretePc in Hinv;
      cbn in Hinv; tauto).
  destruct Hboundary as (Hnb & pc & sourceTrace & Hpc & Hsource & Htrace).
  cbn in Hpc, Hsource, Htrace. rewrite Hpc in HconcretePc.
  inversion HconcretePc as [Hunsigned].
  change (bv_unsigned pc = 0x101d4) in Hunsigned.
  have Hpceq : pc = Z_to_bv 64 0x101d4.
  { rewrite <- (Z_to_bv_bv_unsigned 64 pc), Hunsigned. reflexivity. }
  subst pc.
  have Htable : writeSuccessWithdrawalsInstructionTable global by
    (unfold Inv_memcpy in Hinv; tauto).
  have Hcode : global.(seq_instrs) !! Z_to_bv 64 0x101d4 =
      Some IslaTraces.write_success_02.a101d4.a101d4.
  { apply Htable. unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap. cbn. tauto. }
  rewrite Hcode in Hsource. inversion Hsource. subst sourceTrace.
  subst trace. destruct nb; first discriminate Hnb.
  exists regs, global. reflexivity.
Qed.

Print Assumptions writeSuccessMemcpyEntryShape.
