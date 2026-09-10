From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import IslaTraces.write_success_05.instrs.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Local Existing Instance subsume_instr_some_pre_inst | 1.

Record ByteListItem : Type := {
  byteListData : bv 64;
  byteListSize : bv 64;
  byteListBytes : list (bv 8)
}.

Fixpoint byteListItemResources `{!islaG Sigma} (address : Z)
    (items : list ByteListItem) : iProp Sigma :=
  match items with
  | [] => True
  | item :: rest =>
      (address ↦ₘ byteListData item ∗
       (address + 8) ↦ₘ byteListSize item ∗
       bv_unsigned (byteListData item) ↦ₘ∗ byteListBytes item ∗
       ⌜bv_unsigned (byteListSize item) = length (byteListBytes item)⌝ ∗
       byteListItemResources (address + 16) rest)%I
  end.

Global Instance : LithiumUnfold (@byteListItemResources) := I.

Lemma byteListItemResources_app `{!islaG Sigma} (address : Z)
    (left right : list ByteListItem) :
  byteListItemResources address (left ++ right) -∗
  byteListItemResources address left ∗
  byteListItemResources (address + 16 * Z.of_nat (length left)) right.
Proof.
  iInduction left as [|item left] "IH" forall (address); simpl.
  - iIntros "Hright". iSplit; first done.
    replace (address + 16 * 0%nat)%Z with address by lia.
    iExact "Hright".
  - iIntros "Hresources".
    iDestruct "Hresources" as "(Hdata & Hsize & Hbytes & %Hlength & Hrest)".
    iDestruct ("IH" $! (address + 16)%Z with "Hrest") as "[Hleft Hright]".
    iSplitL "Hdata Hsize Hbytes Hleft".
    { iFrame. done. }
    replace (address + 16 + 16 * Z.of_nat (length left))%Z with
      (address + 16 * Z.of_nat (length (item :: left)))%Z by (simpl; lia).
    iExact "Hright".
Qed.

Lemma byteListItemResources_app_combine `{!islaG Sigma} (address : Z)
    (left right : list ByteListItem) :
  byteListItemResources address left -∗
  byteListItemResources (address + 16 * Z.of_nat (length left)) right -∗
  byteListItemResources address (left ++ right).
Proof.
  iInduction left as [|item left] "IH" forall (address); simpl.
  - iIntros "_ Hright".
    have Hzero : (address + 16 * 0%nat)%Z = address by lia.
    iEval (rewrite Hzero) in "Hright".
    iExact "Hright".
  - iIntros "Hleft Hright".
    iDestruct "Hleft" as "(Hdata & Hsize & Hbytes & %Hlength & Hleft)".
    iFrame.
    iSplit; first done.
    have Haddress :
      (address + 16 * Z.of_nat (length (item :: left)))%Z =
      (address + 16 + 16 * Z.of_nat (length left))%Z by (simpl; lia).
    iEval (rewrite Haddress) in "Hright".
    iPoseProof ("IH" $! (address + 16)%Z with "Hleft Hright") as "Hcombined".
    iExact "Hcombined".
Qed.

Definition byteListProcessedResources `{!islaG Sigma} (address : Z)
    (items : list ByteListItem) : iProp Sigma :=
  byteListItemResources address items.

Lemma byteListProcessedResources_combine `{!islaG Sigma} (address : Z)
    (left right : list ByteListItem) :
  byteListProcessedResources address left -∗
  byteListItemResources (address + 16 * Z.of_nat (length left)) right -∗
  byteListItemResources address (left ++ right).
Proof.
  rewrite /byteListProcessedResources.
  apply byteListItemResources_app_combine.
Qed.

Lemma byteListProcessedResources_snoc `{!islaG Sigma} (address : Z)
    (items : list ByteListItem) (item : ByteListItem) :
  byteListProcessedResources address items -∗
  byteListItemResources (address + 16 * Z.of_nat (length items)) [item] -∗
  byteListProcessedResources address (items ++ [item]).
Proof.
  rewrite /byteListProcessedResources.
  apply byteListItemResources_app_combine.
Qed.

Lemma byteListProcessedResources_nil `{!islaG Sigma} (address : Z) :
  ⊢ byteListProcessedResources address [].
Proof. rewrite /byteListProcessedResources /=. done. Qed.

Global Opaque byteListProcessedResources.

Fixpoint byteListItemEvents (sp : bv 64) (items : list ByteListItem)
    (tail : spec) : spec :=
  match items with
  | [] => tail
  | item :: rest =>
      writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents (byteListData item) (byteListSize item)
          (byteListItemEvents sp rest tail))
  end.

Definition byteListsLoopOtherRegisters : list string :=
  ["x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition byteListsLoopOtherRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> byteListsLoopOtherRegisters.

Definition byteListsLoopExitFrame `{!islaG Sigma} `{!threadG}
    (sp savedRa savedS0 savedS1 finalPointer : bv 64) (itemBase : Z)
    (items : list ByteListItem)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col byteListsLoopOtherRegShapes ∗
   "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x9" ↦ᵣ RVal_Bits finalPointer ∗
   "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp + 24) ↦ₘ savedRa ∗
   (bv_unsigned sp + 16) ↦ₘ savedS0 ∗
   (bv_unsigned sp + 8) ↦ₘ savedS1 ∗
   byteListItemResources itemBase items ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@byteListsLoopExitFrame) := I.

Definition byteListsLoopExit `{!islaG Sigma} `{!threadG}
    (sp savedRa savedS0 savedS1 finalPointer : bv 64) (itemBase : Z)
    (items : list ByteListItem)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗
   byteListsLoopExitFrame sp savedRa savedS0 savedS1 finalPointer
     itemBase items tail P)%I.

Global Instance : LithiumUnfold (@byteListsLoopExit) := I.

Definition byteListEndPointer (pointer : bv 64)
    (items : list ByteListItem) : bv 64 :=
  (pointer + Z_to_bv 64 (8 + 16 * Z.of_nat (length items)))%bv.

Definition byteListsLoopFrame `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (sp savedRa savedS0 savedS1 pointer : bv 64)
    (itemBase : Z) (done : list ByteListItem) (item : ByteListItem)
    (rest : list ByteListItem) (tail : spec) : iProp Sigma :=
  (reg_col byteListsLoopOtherRegShapes ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x9" ↦ᵣ RVal_Bits (pointer + BV 64 8)%bv ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 24) ↦ₘ savedRa ∗
    (bv_unsigned sp + 16) ↦ₘ savedS0 ∗
    (bv_unsigned sp + 8) ↦ₘ savedS1 ∗
    byteListProcessedResources itemBase done ∗
    byteListItemResources (bv_unsigned pointer) (item :: rest) ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (byteListItemEvents sp (item :: rest) tail) ∗
    ⌜S (length rest) < 2 ^ 64⌝ ∗
    ⌜bv_unsigned pointer =
      (itemBase + 16 * Z.of_nat (length done))%Z⌝ ∗
    ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + 16 * Z.of_nat (S (length rest)) < 0x40000000⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    P ∗
    instr_pre 0x15c58
      (byteListsLoopExit sp savedRa savedS0 savedS1
        (byteListEndPointer pointer (item :: rest)) itemBase
        (done ++ item :: rest) tail P) ∗
    True)%I.

Global Instance : LithiumUnfold (@byteListsLoopFrame) := I.

Definition byteListsLoopSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp savedRa savedS0 savedS1 pointer : bv 64) (itemBase : Z)
      (done : list ByteListItem) (item : ByteListItem)
      (rest : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
    byteListsLoopFrame P sp savedRa savedS0 savedS1 pointer itemBase
      done item rest tail)%I.

Global Instance : LithiumUnfold (@byteListsLoopSpec) := I.

Definition byteListsAfterCallSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp savedRa savedS0 savedS1 pointer : bv 64) (itemBase : Z)
      (done : list ByteListItem) (item : ByteListItem)
      (rest : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ reg_col byteListsLoopOtherRegShapes ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15c4c) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
    "x9" ↦ᵣ RVal_Bits (pointer + BV 64 8)%bv ∗
    "x10" ↦ᵣ RVal_Bits (byteListData item) ∗
    "x11" ↦ᵣ RVal_Bits (byteListSize item) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 24) ↦ₘ savedRa ∗
    (bv_unsigned sp + 16) ↦ₘ savedS0 ∗
    (bv_unsigned sp + 8) ↦ₘ savedS1 ∗
    byteListProcessedResources itemBase done ∗
    bv_unsigned pointer ↦ₘ byteListData item ∗
    (bv_unsigned pointer + 8) ↦ₘ byteListSize item ∗
    bv_unsigned (byteListData item) ↦ₘ∗ byteListBytes item ∗
    ⌜bv_unsigned (byteListSize item) = length (byteListBytes item)⌝ ∗
    byteListItemResources (bv_unsigned pointer + 16) rest ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (byteListItemEvents sp rest tail) ∗ P ∗
    ⌜S (length rest) < 2 ^ 64⌝ ∗
    ⌜bv_unsigned pointer =
      (itemBase + 16 * Z.of_nat (length done))%Z⌝ ∗
    ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + 16 * Z.of_nat (S (length rest)) < 0x40000000⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    □ instr_pre 0x15c3c (byteListsLoopSpec P) ∗
    instr_pre 0x15c58
      (byteListsLoopExit sp savedRa savedS0 savedS1
        (byteListEndPointer pointer (item :: rest)) itemBase
        (done ++ item :: rest) tail P) ∗
    True)%I.

Global Instance : LithiumUnfold (@byteListsAfterCallSpec) := I.

Lemma write_success_byte_lists_after_call `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c4c (byteListsAfterCallSpec P).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try match goal with
    | Hsp : bv_extract 0 4 ?stack = 0%bv |-
        bv_unsigned ?stack `mod` 16 = 0 =>
        bv_simplify_arith Hsp; bv_solve
    end.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: destruct rest as [|next more].
  all: try (unfold byteListEndPointer; bv_solve).
  all: try match goal with
    | Hbound : _ < 2 ^ 64, Heq : _ = 0%bv |- _ =>
        exfalso; cbn in Hbound, Heq; contradict Heq; bv_solve
    end.
  all: try match goal with
    | Hneq : _ <> 0%bv |- _ => exfalso; apply Hneq; bv_solve
    end.
  all: try (cbn; done).
  2: {
    rename select (bv_unsigned pointer = _)%Z into Hposition.
    iDestruct select (byteListProcessedResources itemBase done) as "Hdone".
    iDestruct select (bv_unsigned pointer ↦ₘ byteListData item)%I as "Hdata".
    iDestruct select ((bv_unsigned pointer + 8) ↦ₘ byteListSize item)%I
      as "Hsize".
    iDestruct select
      (bv_unsigned (byteListData item) ↦ₘ∗ byteListBytes item)%I as "Hbytes".
    iSplitL "Hdone Hdata Hsize Hbytes".
    - iApply (byteListProcessedResources_combine itemBase done [item]
        with "Hdone").
      simpl. rewrite <- Hposition.
      iFrame. iSplit; first done. done.
    - iFrame. done.
  }
  iExists
      (tail, more, next, done ++ [item], itemBase,
       (pointer + BV 64 16)%bv,
       savedS1, savedS0, savedRa, sp, tt)ₗ.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  have Hpointer : bv_unsigned (pointer + BV 64 16)%bv =
      bv_unsigned pointer + 16 by bv_solve.
  rewrite Hpointer.
  have Hend : byteListEndPointer (pointer + BV 64 16)%bv (next :: more) =
      byteListEndPointer pointer (item :: next :: more) by
    unfold byteListEndPointer; bv_solve.
  rewrite Hend.
  iDestruct select
      ((bv_unsigned pointer + 16) ↦ₘ byteListData next ∗ _)%I
    as "(HnextData & Hrest)".
  iDestruct "Hrest"
    as "(HnextSize & HnextBytes & %HnextLength & Hmore)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try iFrame.
  all: try (unfold byteListEndPointer; bv_solve).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: try iFrame.
  all: try (bv_simplify_arith H1; bv_solve).
  all: try bv_solve.
  all: try lia.
  all: try (cbn in H0; lia).
  all: try match goal with
    | Hbound : context [length (?head :: ?tail)] |- _ =>
        cbn in Hbound; lia
    end.
  all: try (cbn in H3; lia).
  rename select (bv_unsigned pointer = _)%Z into Hposition.
  iDestruct select (byteListProcessedResources itemBase done) as "Hdone".
  iDestruct select (bv_unsigned pointer ↦ₘ byteListData item)%I as "Hdata".
  iDestruct select ((bv_unsigned pointer + 8) ↦ₘ byteListSize item)%I
    as "Hsize".
  iDestruct select
    (bv_unsigned (byteListData item) ↦ₘ∗ byteListBytes item)%I as "Hbytes".
  iSplitL "Hdone Hdata Hsize Hbytes".
  - iApply (byteListProcessedResources_snoc itemBase done item with "Hdone").
    simpl. rewrite <- Hposition.
    iFrame. iSplit; first done. done.
  - rewrite <- app_assoc. simpl.
    iFrame.
    repeat iSplit.
    all: try iAssumption.
    all: iPureIntro.
    all: try assumption.
    all: try match goal with
      | Hbound : S (length (?head :: ?rest)) < 2 ^ 64 |- _ =>
          cbn in Hbound; lia
      end.
    all: try (cbn in *; lia).
    all: try (rewrite app_length; simpl; lia).
    all: try
      (bv_simplify_arith select (bv_extract 0 3 pointer = _); bv_solve).
    all: try bv_solve.
    all: try lia.
  all: lazymatch goal with |- ?G => fail "byteLists continuation residual" G end.
Qed.

Lemma write_success_byte_lists_loop `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  □ instr_pre 0x15c3c (byteListsLoopSpec P) -∗
  instr_body 0x15c3c (byteListsLoopSpec P).
Proof.
  iStartProof. iIntros "#Hcode #Hencoder #Hloop".
  iEval (simpl) in "Hcode".
  iDestruct "Hcode" as "(? & ?)".
  repeat iDestruct select (_ ∗ _)%I as "(? & ?)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try (bv_simplify_arith H2; bv_solve).
  all: try
    (bv_simplify_arith select (bv_extract 0 3 pointer = _); bv_solve).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  iExists
    (byteListItemEvents sp rest tail, byteListBytes item, 0x15c4c%Z,
     (pointer + BV 64 8)%bv,
     Z_to_bv 64 (Z.of_nat (S (length rest))), sp,
     byteListSize item, byteListData item, tt)ₗ.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try match goal with
    | Hsp : bv_extract 0 4 ?stack = 0%bv |-
        bv_unsigned ?stack `mod` 16 = 0 =>
        bv_simplify_arith Hsp; bv_solve
    end.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  iSplitL; last done.
  iIntros "Hreturn HPC".
  iEval (simpl) in "Hreturn".
  iDestruct "Hreturn" as "(? & ?)".
  repeat iDestruct select (_ ∗ _)%I as "(? & ?)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: liShow.
  all: destruct rest as [|next more].
  all: try (unfold byteListEndPointer; bv_solve).
  all: try match goal with
    | Hbound : _ < 2 ^ 64, Heq : _ = 0%bv |- _ =>
        exfalso; cbn in Hbound, Heq; contradict Heq; bv_solve
    end.
  all: try match goal with
    | Hneq : _ <> 0%bv |- _ => exfalso; apply Hneq; bv_solve
    end.
  all: try (cbn; done).
  2: {
    rename select (bv_unsigned pointer = _)%Z into Hposition.
    iDestruct select (byteListProcessedResources itemBase done) as "Hdone".
    iDestruct select (_ ↦ₘ byteListData item)%I as "Hdata".
    iDestruct select (_ ↦ₘ byteListSize item)%I as "Hsize".
    have HdataAddress : bv_unsigned LET0 = bv_unsigned pointer by bv_solve.
    have HsizeAddress : bv_unsigned LET5 = bv_unsigned pointer + 8 by bv_solve.
    iEval (rewrite HdataAddress) in "Hdata".
    iEval (rewrite HsizeAddress) in "Hsize".
    iDestruct select
      (bv_unsigned (byteListData item) ↦ₘ∗ byteListBytes item)%I as "Hbytes".
    iSplitL "Hdone Hdata Hsize Hbytes".
    - iApply (byteListProcessedResources_combine itemBase done [item]
        with "Hdone").
      simpl. rewrite <- Hposition.
      iFrame. done.
    - iFrame.
  }
  iExists
      (tail, more, next, done ++ [item], itemBase,
       (pointer + BV 64 16)%bv,
       savedS1, savedS0, savedRa, sp, tt)ₗ.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  have Hpointer : bv_unsigned (pointer + BV 64 16)%bv =
      bv_unsigned pointer + 16 by bv_solve.
  rewrite Hpointer.
  have Hend : byteListEndPointer (pointer + BV 64 16)%bv (next :: more) =
      byteListEndPointer pointer (item :: next :: more) by
    unfold byteListEndPointer; bv_solve.
  rewrite Hend.
  iDestruct select
      ((bv_unsigned pointer + 16) ↦ₘ byteListData next ∗ _)%I
    as "(HnextData & Hrest)".
  iDestruct "Hrest"
    as "(HnextSize & HnextBytes & %HnextLength & Hmore)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try iFrame.
  all: try (bv_simplify_arith select (bv_extract 0 3 pointer = _); bv_solve).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: try iFrame.
  all: try (bv_simplify_arith select (bv_extract 0 3 pointer = _); bv_solve).
  all: try bv_solve.
  all: try lia.
  all: try match goal with
    | Hbound : S (length (?next :: ?more)) < 2 ^ 64 |-
        S (length ?more) < 2 ^ 64 => cbn in Hbound; lia
    end.
  all: try (cbn in H0; lia).
  all: try match goal with
    | Hbound : context [length (?head :: ?tail)] |- _ =>
        cbn in Hbound; lia
    end.
  rename select (bv_unsigned pointer = _)%Z into Hposition.
  iDestruct select (byteListProcessedResources itemBase done) as "Hdone".
  iDestruct select (_ ↦ₘ byteListData item)%I as "Hdata".
  iDestruct select (_ ↦ₘ byteListSize item)%I as "Hsize".
  have HdataAddress : bv_unsigned LET0 = bv_unsigned pointer by bv_solve.
  have HsizeAddress : bv_unsigned LET5 = bv_unsigned pointer + 8 by bv_solve.
  iEval (rewrite HdataAddress) in "Hdata".
  iEval (rewrite HsizeAddress) in "Hsize".
  iDestruct select
    (bv_unsigned (byteListData item) ↦ₘ∗ byteListBytes item)%I as "Hbytes".
  iSplitL "Hdone Hdata Hsize Hbytes".
  - iApply (byteListProcessedResources_snoc itemBase done item with "Hdone").
    simpl. rewrite <- Hposition.
    iFrame. iSplit; first done. done.
  - rewrite <- app_assoc. simpl.
    iFrame.
    repeat iSplit.
    all: try iAssumption.
    all: iPureIntro.
    all: try assumption.
    all: try (cbn in *; lia).
    all: try (rewrite app_length; simpl; lia).
    all: try
      (bv_simplify_arith select (bv_extract 0 3 pointer = _); bv_solve).
    all: try bv_solve.
    all: try lia.
  all: lazymatch goal with |- ?G => fail "byteLists loop residual" G end.
Qed.

Lemma write_success_byte_lists_loop_pre `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  □ instr_pre 0x15c3c (byteListsLoopSpec P).
Proof.
  iStartProof. iIntros "#Hcode #Hencoder".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_byte_lists_loop P with "Hcode Hencoder IH").
Qed.

Definition zesuEncoderByteListsCallSpec `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (zesu_c_call 80
    (fun args sp RET =>
      ∃ (items : list ByteListItem) (tail : spec),
      byteListItemResources (bv_unsigned (args !!! 0%nat)) items ∗
      mmio_range 0x2401a0c0 16 ∗
      spec_trace
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
          (byteListItemEvents (sp - BV 64 32)%bv items tail)) ∗
      ⌜bv_unsigned (args !!! 1%nat) = length items⌝ ∗
      ⌜length items < 2 ^ 64⌝ ∗
      ⌜bv_extract 0 3 (args !!! 0%nat) = BV 3 0⌝ ∗
      ⌜0x20000000 <= bv_unsigned (args !!! 0%nat)⌝ ∗
      ⌜bv_unsigned (args !!! 0%nat) + 16 * Z.of_nat (length items) <
        0x40000000⌝ ∗
      ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
      ⌜0x20000000 <= bv_unsigned sp - 80⌝ ∗
      ⌜bv_unsigned sp < 0x40000000⌝ ∗
      RET (fun _ =>
        byteListItemResources (bv_unsigned (args !!! 0%nat)) items ∗
        mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I.

Global Instance : LithiumUnfold (@zesuEncoderByteListsCallSpec) := I.

Local Remove Hints subsume_instr_some_pre_inst : typeclass_instances.
Lemma byte_lists_ret_address (ret : bv 64) :
  bv_extract 0 1 ret = BV 1 0 ->
  bv_unsigned
    (bv_or (bv_and (bv_sign_extend 64 ret + 0)%bv
      (BV 64 18446744073709551614)) (BV 64 0)) = bv_unsigned ret.
Proof.
  move => Hret. rewrite bv_sign_extend_idemp.
  have -> : (ret + 0)%bv = ret by bv_solve.
  f_equal. bv_simplify. bv_simplify Hret.
  bitblast as i. by bitblast Hret with i.
Qed.

Definition byteListsSavedRegisters : list string :=
  ["x18"; "x19"; "x20"; "x21"; "x22";
   "x23"; "x24"; "x25"; "x26"; "x27"].

Definition byteListsCode `{!islaG Sigma} : iProp Sigma :=
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I.

Lemma byteListsCode_intro `{!islaG Sigma} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗ byteListsCode.
Proof. iIntros "Hcode". iExact "Hcode". Qed.

Lemma byteListsCode_elim `{!islaG Sigma} :
  byteListsCode -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I.
Proof. iIntros "Hcode". iExact "Hcode". Qed.

Global Opaque byteListsCode.

Definition byteListsEmptyBranchSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗ P ∗
   instr_pre 0x15c58
     (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗ P) ∗
   True)%I.

Global Instance : LithiumUnfold (@byteListsEmptyBranchSpec) := I.

Lemma byte_lists_empty_branch `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x15c38 (Some IslaTraces.write_success_05.a15c38.a15c38) -∗
  instr_body 0x15c38 (byteListsEmptyBranchSpec P).
Proof.
  iStartProof.
  repeat (liAStep; close_infeasible_bv_branches).
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try close_infeasible_bv_branches.
  all: try match goal with
  | Hneq : ?count <> 0%bv |- _ => exfalso; apply Hneq; bv_solve
  end.
  all: try bv_solve.
  all: try iFrame.
  Unshelve.
  all: try iFrame.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try close_infeasible_bv_branches.
  all: try match goal with
  | Hneq : ?count <> 0%bv |- _ => exfalso; apply Hneq; bv_solve
  end.
  all: try bv_solve.
  all: try iFrame.
Qed.

Lemma byte_lists_empty_branch_pre `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x15c38 (Some IslaTraces.write_success_05.a15c38.a15c38) -∗
  □ instr_pre 0x15c38 (byteListsEmptyBranchSpec P).
Proof.
  iStartProof. iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext. iApply byte_lists_empty_branch.
  iExact "Hcode".
Qed.

Definition byteListsNonemptyBranchSpec `{!islaG Sigma} `{!threadG}
    (count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits count ∗ P ∗
   ⌜count <> BV 64 0⌝ ∗
   instr_pre 0x15c3c
     (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits count ∗ P) ∗ True)%I.

Global Instance : LithiumUnfold (@byteListsNonemptyBranchSpec) := I.

Lemma byte_lists_nonempty_branch `{!islaG Sigma} `{!threadG}
    (count : bv 64) (P : iProp Sigma) :
  instr 0x15c38 (Some IslaTraces.write_success_05.a15c38.a15c38) -∗
  instr_body 0x15c38 (byteListsNonemptyBranchSpec count P).
Proof.
  iStartProof.
  repeat (liAStep; close_infeasible_bv_branches).
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try close_infeasible_bv_branches.
  all: try match goal with
  | Hneq : ?count <> 0%bv |- _ => exfalso; apply Hneq; bv_solve
  end.
  all: try bv_solve.
  all: try iFrame.
  Unshelve.
  all: try iFrame.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try close_infeasible_bv_branches.
  all: try match goal with
  | Hneq : ?count <> 0%bv |- _ => exfalso; apply Hneq; bv_solve
  end.
  all: try bv_solve.
  all: try iFrame.
  Unshelve.
Qed.

Lemma byte_lists_nonempty_branch_pre `{!islaG Sigma} `{!threadG}
    (count : bv 64) (P : iProp Sigma) :
  instr 0x15c38 (Some IslaTraces.write_success_05.a15c38.a15c38) -∗
  □ instr_pre 0x15c38 (byteListsNonemptyBranchSpec count P).
Proof.
  iStartProof. iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply byte_lists_nonempty_branch. iExact "Hcode".
Qed.

Definition byteListsPublicFrame `{!islaG Sigma} `{!threadG}
    (callerSp ret savedS0 savedS1 : bv 64) (saved : list valu)
    (base : Z) (items : list ByteListItem) (tail : spec) : iProp Sigma :=
  (reg_col (zip_with (fun register value => (KindReg register, ExactShape value))
      byteListsSavedRegisters saved) ∗
   (bv_unsigned callerSp - 32) ↦ₘ? 8 ∗
   instr_pre (bv_unsigned ret)
     (zesu_c_call_ret 80
       (RVal_Bits savedS0 :: RVal_Bits savedS1 :: saved)
       ret callerSp
       (fun _ => byteListItemResources base items ∗
         mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)) ∗ True)%I.

Global Instance : LithiumUnfold (@byteListsPublicFrame) := I.

Lemma write_success_byte_lists_epilogue `{!islaG Sigma} `{!threadG}
    (callerSp ret savedS0 savedS1 finalPointer : bv 64)
    (saved : list valu) (base : Z) (items : list ByteListItem) (tail : spec)
    (Hcaller : bv_extract 0 4 callerSp = BV 4 0)
    (Hmin : 0x20000000 <= bv_unsigned callerSp - 80)
    (Hmax : bv_unsigned callerSp < 0x40000000)
    (Hret1 : bv_extract 0 1 ret = BV 1 0)
    (Hret : bv_extract 0 2 ret = BV 2 0) :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c58
    (byteListsLoopExit (callerSp - BV 64 32)%bv ret savedS0 savedS1
      finalPointer base items tail
      (byteListsPublicFrame callerSp ret savedS0 savedS1 saved
        base items tail)).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_idemp.
  all: try (change (bv_extract 0 2 ret = BV 2 0); exact Hret).
  all: try (bv_simplify_arith Hcaller; bv_solve).
  all: try (bv_simplify_arith Hcaller; lia).
  all: try
    (bv_simplify_arith select
      (bv_extract 0 4 (callerSp - BV 64 32)%bv = _); bv_solve).
  all: try match goal with
  | Hstack : bv_extract 0 4 ?stack = 0%bv |- _ =>
      bv_simplify_arith Hstack; bv_solve
  end.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: try (rewrite (byte_lists_ret_address ret Hret1); liARun).
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  Unshelve.
Qed.

Lemma byte_lists_epilogue_pre `{!islaG Sigma} `{!threadG}
    (callerSp ret savedS0 savedS1 finalPointer : bv 64)
    (saved : list valu) (base : Z) (items : list ByteListItem) (tail : spec)
    (Hcaller : bv_extract 0 4 callerSp = BV 4 0)
    (Hmin : 0x20000000 <= bv_unsigned callerSp - 80)
    (Hmax : bv_unsigned callerSp < 0x40000000)
    (Hret1 : bv_extract 0 1 ret = BV 1 0)
    (Hret : bv_extract 0 2 ret = BV 2 0) :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c58
    (byteListsLoopExit (callerSp - BV 64 32)%bv ret savedS0 savedS1
      finalPointer base items tail
      (byteListsPublicFrame callerSp ret savedS0 savedS1 saved
        base items tail)).
Proof.
  iStartProof. iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply (write_success_byte_lists_epilogue callerSp ret savedS0 savedS1
    finalPointer saved base items tail Hcaller Hmin Hmax Hret1 Hret).
  iExact "Hcode".
Qed.

Lemma write_success_byte_lists `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x15c10 zesuEncoderByteListsCallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Hint #Hbytes".
  iPoseProof (byteListsCode_intro with "Hcode") as "#HsavedCode".
  iPoseProof "Hcode" as "#HcodeSteps".
  iEval (simpl) in "HcodeSteps".
  iDestruct "HcodeSteps" as "(? & ?)".
  repeat iDestruct select (_ ∗ _)%I as "(? & ?)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try rewrite bv_sign_extend_idemp.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: try
    (bv_simplify_arith select (bv_extract 0 3 b10 = _); bv_solve).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  rename select (bv_extract 0 4 sp = BV 4 0) into HspAligned.
  rename select (0x20000000 <= bv_unsigned sp - 80) into HspMin.
  rename select (bv_unsigned sp < 0x40000000) into HspMax.
  rename select (bv_extract 0 1 ret = BV 1 0) into Hret1.
  rename select (bv_extract 0 2 ret = BV 2 0) into Hret2.
  have -> : LET0 = (sp - BV 64 32)%bv by bv_solve.
  have -> : LET2 = (sp - BV 64 8)%bv by bv_solve.
  have -> : LET6 = (sp - BV 64 16)%bv by bv_solve.
  have -> : LET10 = (sp - BV 64 24)%bv by bv_solve.
  iExists
    (byteListItemEvents (sp - BV 64 32)%bv items tail,
     0x15c34%Z, LET0, b11, tt)ₗ.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  iApply subsume_instr_some_pre.
  iExists tt.
  iSplitL; last done.
  iIntros "Hreturn HPC".
  iEval (simpl) in "Hreturn".
  iDestruct "Hreturn" as "(? & ?)".
  repeat iDestruct select (_ ∗ _)%I as "(? & ?)".
  have -> : LET0 = (sp - BV 64 32)%bv by bv_solve.
  have -> : LET14 = b11 by bv_solve.
  have -> : LET16 = b10 by bv_solve.
  rename select (bv_unsigned b11 = length items) into Hcount.
  destruct items as [|item rest].
  - have Hb11 : b11 = BV 64 0.
    { apply bv_eq. rewrite bv_unsigned_BV. cbn in Hcount. lia. }
    subst b11.
    iPoseProof (byteListsCode_elim with "HsavedCode") as "#HcodeAgain".
    iPoseProof (byte_lists_epilogue_pre sp ret b b0
      (byteListEndPointer b10 [])
      [RVal_Bits b1; RVal_Bits b2; RVal_Bits b3; RVal_Bits b4;
       RVal_Bits b5; RVal_Bits b6; RVal_Bits b7; RVal_Bits b8;
       RVal_Bits b9; RVal_Bits b18]
      (bv_unsigned b10) [] tail HspAligned HspMin HspMax Hret1 Hret2
      with "HcodeAgain") as "#Hepilogue".
    iDestruct select ("x8" ↦ᵣ RVal_Bits _)%I as "Hx8".
    repeat iClear select (instr 0x15c38 _).
    iClear "HcodeAgain".
    liARun.
    have -> : LET25 = (b10 + BV 64 8)%bv by bv_solve.
    iPoseProof (byteListsCode_elim with "HsavedCode") as "#HbranchCodes".
    iEval (simpl) in "HbranchCodes".
    iDestruct "HbranchCodes" as "(? & ?)".
    repeat iDestruct select (_ ∗ _)%I as "(? & ?)".
    iDestruct select (instr 0x15c38 _) as "#HbranchCode".
    iPoseProof (byte_lists_empty_branch_pre
      (byteListsLoopExitFrame (sp - BV 64 32)%bv ret b b0
        (byteListEndPointer b10 []) (bv_unsigned b10) [] tail
        (byteListsPublicFrame sp ret b b0
          [RVal_Bits b1; RVal_Bits b2; RVal_Bits b3; RVal_Bits b4;
           RVal_Bits b5; RVal_Bits b6; RVal_Bits b7; RVal_Bits b8;
           RVal_Bits b9; RVal_Bits b18]
          (bv_unsigned b10) [] tail)) with
      "HbranchCode") as "#HemptyBranch".
    iClear "HbranchCode".
    liARun.
    Unshelve. all: prepare_sidecond.
    all: try assumption.
    all: try rewrite bv_sign_extend_idemp.
    all: try close_infeasible_bv_branches.
    all: try iFrame.
    all: try bv_solve.
    all: try lia.
    Unshelve.
  - have Hb11 : b11 <> BV 64 0.
    { move => Hzero. subst b11. rewrite bv_unsigned_BV in Hcount.
      cbn in Hcount. lia. }
    iDestruct select
      (bv_unsigned b10 ↦ₘ byteListData item ∗ _)%I
      as "(HitemData & HitemSize & HitemBytes & %HitemLength & HitemsRest)".
    iAssert (byteListItemResources (bv_unsigned b10) (item :: rest))
      with "[HitemData HitemSize HitemBytes HitemsRest]" as "Hitems".
    { simpl. iFrame. done. }
    pose (saved :=
      [RVal_Bits b1; RVal_Bits b2; RVal_Bits b3; RVal_Bits b4;
       RVal_Bits b5; RVal_Bits b6; RVal_Bits b7; RVal_Bits b8;
       RVal_Bits b9; RVal_Bits b18]).
    pose (P := byteListsPublicFrame sp ret b b0 saved
      (bv_unsigned b10) (item :: rest) tail).
    iPoseProof (byteListsCode_elim with "HsavedCode") as "#HcodeAgain".
    iPoseProof (byte_lists_epilogue_pre sp ret b b0
      (byteListEndPointer b10 (item :: rest)) saved
      (bv_unsigned b10) (item :: rest) tail HspAligned HspMin HspMax
      Hret1 Hret2 with "HcodeAgain") as "#Hepilogue".
    iPoseProof (write_success_byte_lists_loop_pre P
      with "HcodeAgain Hbytes") as "#Hloop".
    have Hb11Count : b11 = Z_to_bv 64 (Z.of_nat (S (length rest))).
    { apply bv_eq. cbn in Hcount. bv_solve. }
    iAssert (instr_pre 0x15c3c
      (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits b11 ∗
       byteListsLoopFrame P (sp - BV 64 32)%bv ret b b0 b10
         (bv_unsigned b10) [] item rest tail))%I
      with "[Hloop]" as "#HloopConcrete".
    { iApply (instr_pre_wand 0x15c3c 0x15c3c true true with "Hloop");
        [done | done |].
      iIntros "Hstate".
      rewrite /byteListsLoopSpec.
      iExists (sp - BV 64 32)%bv, ret, b, b0, b10,
        (bv_unsigned b10), [], item, rest, tail.
      rewrite <- Hb11Count. iExact "Hstate". }
    iPoseProof (byteListProcessedResources_nil (bv_unsigned b10)) as "Hdone".
    repeat iClear select (instr 0x15c38 _).
    iClear "HcodeAgain".
    liARun.
    have -> : LET25 = (b10 + BV 64 8)%bv by bv_solve.
    iPoseProof (byteListsCode_elim with "HsavedCode") as "#HbranchCodes".
    iEval (simpl) in "HbranchCodes".
    iDestruct "HbranchCodes" as "(? & ?)".
    repeat iDestruct select (_ ∗ _)%I as "(? & ?)".
    iDestruct select (instr 0x15c38 _) as "#HbranchCode".
    iPoseProof (byte_lists_nonempty_branch_pre
      (Z_to_bv 64 (Z.of_nat (S (length rest))))
      (byteListsLoopFrame P (sp - BV 64 32)%bv ret b b0 b10
        (bv_unsigned b10) [] item rest tail) with
      "HbranchCode") as "#HnonemptyBranch".
    iClear "HbranchCode".
    liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try rewrite bv_sign_extend_idemp.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: try
    (bv_simplify_arith select (bv_extract 0 3 b10 = _); bv_solve).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: try match goal with
  | Hneq : ?count <> 0%bv |- _ =>
      exfalso; apply Hneq; bv_solve
  end.
  all: try unLET.
  all: try rewrite bv_sign_extend_idemp.
  all: try (bv_simplify_arith select (bv_extract 0 2 ret = _); bv_solve).
  all: try (rewrite (byte_lists_ret_address ret ltac:(assumption)); liARun).
  all: try liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
Qed.
