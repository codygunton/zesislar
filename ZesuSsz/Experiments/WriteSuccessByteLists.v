From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccess.
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
  ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Definition byteListsLoopOtherRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> byteListsLoopOtherRegisters.

Definition byteListsLoopExit `{!islaG Sigma} `{!threadG}
    (sp savedRa savedS0 savedS1 finalPointer : bv 64) (itemBase : Z)
    (items : list ByteListItem)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col byteListsLoopOtherRegShapes ∗
   "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗ "x9" ↦ᵣ RVal_Bits finalPointer ∗
   "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp + 24) ↦ₘ savedRa ∗
   (bv_unsigned sp + 16) ↦ₘ savedS0 ∗
   (bv_unsigned sp + 8) ↦ₘ savedS1 ∗
   byteListItemResources itemBase items ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@byteListsLoopExit) := I.

Definition byteListEndPointer (pointer : bv 64)
    (items : list ByteListItem) : bv 64 :=
  (pointer + Z_to_bv 64 (8 + 16 * Z.of_nat (length items)))%bv.

Definition byteListsLoopSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp savedRa savedS0 savedS1 pointer : bv 64) (itemBase : Z)
      (done : list ByteListItem) (item : ByteListItem)
      (rest : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ reg_col byteListsLoopOtherRegShapes ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
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
  ([∗ list] instruction ∈ IslaTraces.write_success_18.instrs.instr_map,
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
       savedS1, savedS0, savedRa, tt)ₗ.
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
  ([∗ list] instruction ∈ IslaTraces.write_success_18.instrs.instr_map,
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
       savedS1, savedS0, savedRa, tt)ₗ.
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
