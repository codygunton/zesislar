Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Export ZesuSsz.Compliance.DecodeItemDataRegistrations.
Require Export ZesuSsz.Compliance.DecodeItemEmptyStringOutputMeaning.
Require Export ZesuSsz.Compliance.DecodeItemShortListOutputMeaning.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
From Coq Require Import List Lia.
Require Import ZesuSsz.Compliance.DecodeItemOutputWitnessSelections.
Require Import ZesuSsz.Compliance.DecodeItemRawOutputFacts.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.

Import ListNotations.
Open Scope nat_scope.

Lemma decodeItemSliceField (bytes : list byte) offset count :
  fieldImage bytes offset (take count (drop offset bytes)).
Proof.
  intros i Hi. rewrite nth_error_firstn_inside.
  - rewrite nth_error_skipn_offset. reflexivity.
  - rewrite firstn_length in Hi. lia.
Qed.

Lemma decodeItemWordSlice (bytes : list byte) offset value :
  word64At bytes offset value <->
  length (take 8 (drop offset bytes)) = 8 /\
  fieldImage bytes offset (take 8 (drop offset bytes)) /\
  littleEndian (take 8 (drop offset bytes)) = value.
Proof.
  unfold word64At. split.
  - intros [Hlength Hvalue]. split; first exact Hlength.
    split; [apply decodeItemSliceField|exact Hvalue].
  - intros [Hlength [_ Hvalue]]. split; assumption.
Qed.

Lemma decodeItemByteField (bytes : list byte) offset (value : byte) :
  byteAt bytes offset (bv_unsigned value) <-> fieldImage bytes offset [value].
Proof.
  unfold byteAt, fieldImage. split.
  - intros H i Hi. destruct i; [|cbn in Hi; lia].
    rewrite Nat.add_0_r. cbn.
    destruct (nth_error bytes offset) as [actual|] eqn:Hactual;
      rewrite Hactual in H |- *; cbn in H; last discriminate.
    injection H as H. f_equal. apply bv_eq. exact H.
  - intros H. specialize (H 0 ltac:(cbn; lia)).
    rewrite Nat.add_0_r in H. cbn in H. rewrite H. reflexivity.
Qed.

Lemma decodeItemPaddingFields (before after : list byte) :
  (forall i, (17 <= i < 24 \/ 34 <= i < 40) ->
    nth_error after i = nth_error before i) <->
  preservedImage before after 17 7 /\ preservedImage before after 34 6.
Proof.
  split.
  - intros H. split; intros i Hi; apply H; [left|right]; lia.
  - intros [Hfirst Hlast] i [[Hlo Hhi]|[Hlo Hhi]].
    + replace i with (17 + (i-17)) by lia. apply Hfirst. lia.
    + replace i with (34 + (i-34)) by lia. apply Hlast. lia.
Qed.

#[export] Instance decodeItemSuccessSlicesRegistered before after pointer payload isList consumed :
  SimplAnd (successResult40 before after pointer payload isList consumed)
  (length before = 40 /\ length after = 40 /\
   (length (take 8 after) = 8 /\ fieldImage after 0 (take 8 after) /\ littleEndian (take 8 after) = pointer) /\
   (length (take 8 (drop 8 after)) = 8 /\ fieldImage after 8 (take 8 (drop 8 after)) /\ littleEndian (take 8 (drop 8 after)) = payload) /\
   fieldImage after 16 [Z_to_bv 8 (if isList then 1 else 0)] /\
   (length (take 8 (drop 24 after)) = 8 /\ fieldImage after 24 (take 8 (drop 24 after)) /\ littleEndian (take 8 (drop 24 after)) = consumed) /\
   fieldImage after 32 [Z_to_bv 8 0] /\ fieldImage after 33 [Z_to_bv 8 0] /\
   preservedImage before after 17 7 /\ preservedImage before after 34 6).
Proof.
  unfold SimplAnd, successResult40.
  rewrite <- (decodeItemWordSlice after 0 pointer).
  rewrite <- (decodeItemWordSlice after 8 payload).
  rewrite <- (decodeItemWordSlice after 24 consumed).
  rewrite <- (decodeItemByteField after 16 (Z_to_bv 8 (if isList then 1 else 0))%Z).
  rewrite <- (decodeItemByteField after 32 (Z_to_bv 8 0)).
  rewrite <- (decodeItemByteField after 33 (Z_to_bv 8 0)).
  rewrite decodeItemPaddingFields.
  destruct isList; reflexivity.
Qed.

#[export] Instance decodeItemErrorImageRegistered after :
  SimplAnd (errorResult40 after) (after = RlpDecodeItemSchema.errorEncoding).
Proof.
  unfold SimplAnd. split.
  - intros ->. exact (proj1 errorReturnImage).
  - intros Herror. apply fieldImage_entire.
    + rewrite errorEncoding_length. exact (proj1 Herror).
    + intros i Hi. rewrite errorEncoding_length in Hi.
      pose proof (proj2 Herror i Hi) as Hactual.
      pose proof (proj2 (proj1 errorReturnImage) i Hi) as Hexpected.
      unfold byteAt in Hactual, Hexpected.
      destruct (nth_error after i) as [a|] eqn:Ha;
        destruct (nth_error RlpDecodeItemSchema.errorEncoding i) as [b|] eqn:Hb;
        rewrite ?Ha in Hactual |- *; rewrite ?Hb in Hexpected |- *;
        cbn in Hactual, Hexpected; try discriminate.
      f_equal. apply bv_eq.
      injection Hactual as Hactual. injection Hexpected as Hexpected.
      exact (eq_trans Hactual (eq_sym Hexpected)).
Qed.


Open Scope Z_scope.
Lemma decodeItemExitShortListPlusEquations args locals (inputPrefix : bv 8) (rest : list byte) :
 decodeItemInputHead args inputPrefix rest ->
 (192 <= bv_unsigned inputPrefix <= 247)%Z ->
 bv_unsigned (returnA1 locals) = decodeItemInputPointer args ->
 bv_unsigned (returnA3 locals) = bv_unsigned inputPrefix - 192 ->
 decodeItemInputLength args = length (decodeItemInputBytes args) ->
 (0 <= decodeItemInputPointer args)%Z ->
 (decodeItemInputPointer args + decodeItemInputLength args < 2^64)%Z ->
 bv_unsigned ((returnA1 locals + 1)%bv) = decodeItemInputPointer args + 1 /\
 bv_unsigned ((returnA3 locals + 1)%bv) = 1 + (bv_unsigned inputPrefix - 192).
Proof.
 intros Hhead Hprefix Hpointer Hpayload Hlength Hlower Hupper.
 split.
 - assert (Hword : returnA1 locals = Z_to_bv 64 (decodeItemInputPointer args)) by
     (rewrite <- Hpointer; symmetry; apply Z_to_bv_bv_unsigned).
   rewrite Hword. apply (decodeItemRawInputSuccessor args inputPrefix rest); assumption.
 - bv_simplify_arith. rewrite Hpayload.
   rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.

#[export] Instance decodeItemExitShortListPlusDerivedFacts args locals prefix rest :
  ZesuDerivedFacts (decodeItemShortListOutputFacts args locals prefix rest)
    (bv_unsigned ((returnA1 locals + 1)%bv) = decodeItemInputPointer args + 1 /\
     bv_unsigned ((returnA3 locals + 1)%bv) = 1 + (bv_unsigned prefix - 192)).
Proof.
  unfold ZesuDerivedFacts, decodeItemShortListOutputFacts.
  intros (Hdomain & Hstorage & Hhead & Hlo & Hhi & Hpointer & Hpayload &
    Haccepted & Hlink & Hlength & Hlower & Hupper).
  eapply decodeItemExitShortListPlusEquations; eauto.
Qed.

Open Scope nat_scope.
Lemma decodeItemExitWriteField (l bytes : list byte) (k w : nat) :
 k <= length l -> length bytes = w ->
 fieldImage (take k l ++ bytes ++ drop (k+w) l) k bytes.
Proof.
 intros Hk _.
 pose proof (fieldImage_middle (take k l) bytes (drop (k+w) l)) as Hfield.
 rewrite length_take in Hfield.
 rewrite Nat.min_l in Hfield; last exact Hk.
 exact Hfield.
Qed.
Lemma decodeItemExitWriteOutside (l bytes : list byte) (k w i : nat) :
 k <= length l -> length bytes = w -> (i < k \/ k+w <= i) ->
 nth_error (take k l ++ bytes ++ drop (k+w) l) i = nth_error l i.
Proof.
 intros Hk Hw [Hi|Hi];
 assert (Htake : length (take k l) = k) by (rewrite length_take; apply Nat.min_l; exact Hk).
 - rewrite nth_error_app1; last (rewrite Htake; lia).
   apply nth_error_firstn_inside. exact Hi.
 - rewrite nth_error_app2; last (rewrite Htake; lia).
   rewrite nth_error_app2; last (rewrite Htake; lia).
   rewrite nth_error_skipn_offset Htake.
   f_equal. lia.
Qed.
Lemma decodeItemExitWriteFieldKeep (l bytes field : list byte) (k w off : nat) :
 k <= length l -> length bytes = w ->
 (off+length field <= k \/ k+w <= off) -> fieldImage l off field ->
 fieldImage (take k l ++ bytes ++ drop (k+w) l) off field.
Proof.
 intros Hk Hw Hsep Hfield i Hi.
 rewrite decodeItemExitWriteOutside; [apply Hfield; exact Hi|exact Hk|exact Hw|destruct Hsep as [Hsep|Hsep]; [left; eapply Nat.lt_le_trans; [apply Nat.add_lt_mono_l; exact Hi|exact Hsep]|right; eapply Nat.le_trans; [exact Hsep|apply Nat.le_add_r]]].
Qed.
Lemma decodeItemExitWritePreserved (before l bytes : list byte) (k w off count : nat) :
 k <= length l -> length bytes = w ->
 (off+count <= k \/ k+w <= off) -> preservedImage before l off count ->
 preservedImage before (take k l ++ bytes ++ drop (k+w) l) off count.
Proof.
 intros Hk Hw Hsep Hpres i Hi.
 rewrite decodeItemExitWriteOutside; [apply Hpres; exact Hi|exact Hk|exact Hw|destruct Hsep as [Hsep|Hsep]; [left; eapply Nat.lt_le_trans; [apply Nat.add_lt_mono_l; exact Hi|exact Hsep]|right; eapply Nat.le_trans; [exact Hsep|apply Nat.le_add_r]]].
Qed.
Ltac decodeItemExitWriteParts tail original continuation :=
 let rec scan rest acc := lazymatch rest with
 | drop ?ending original => let bytes := eval cbn [List.app] in acc in continuation bytes ending
 | ?head :: ?rest' => scan rest' constr:(acc ++ [head])
 end in scan tail constr:(@nil byte).
Ltac decodeItemExitImageArithmetic :=
 cbn [N.to_nat Pos.to_nat];
 repeat first [progress rewrite length_app | progress rewrite length_take |
   progress rewrite length_drop | progress rewrite length_insert |
   progress unfold word64Bytes | progress rewrite map_length |
   progress rewrite seq_length | progress cbn [length] |
   match goal with H : length ?l = ?n |- context[length ?l] => rewrite H end];
 lia.
Ltac decodeItemExitLiteralField l bytes k off value :=
 is_closed_term bytes; is_closed_term value;
 is_closed_term k; is_closed_term off;
 let index := eval cbv in (off-k)%nat in
 let Hindex := fresh "HliteralIndex" in
 let Hwrite := fresh "HliteralWrite" in
 assert (Hindex : (index < length bytes)%nat) by decodeItemExitImageArithmetic;
 assert (Hwrite : fieldImage (take k l ++ bytes ++ drop (k+length bytes) l) k bytes) by
   (apply decodeItemExitWriteField; [decodeItemExitImageArithmetic|reflexivity]);
 let i := fresh "i" in let Hi := fresh "Hi" in
 unfold fieldImage; intros i Hi; destruct i; last (cbn in Hi; lia);
 rewrite Nat.add_0_r;
 replace off with (k+index)%nat by decodeItemExitImageArithmetic;
 rewrite (Hwrite index Hindex);
 cbn [nth_error]; f_equal; apply bv_eq; reflexivity.

Ltac decodeItemExitImageSolve :=
 repeat match goal with |- context [(?base + ?offset - ?base)%Z] =>
   replace (base+offset-base)%Z with offset by (Zify.zify; xlia zchecker) end;
 first [assumption | lazymatch goal with
 | |- fieldImage (take ?k ?l ++ ?tail) ?off ?field =>
   decodeItemExitWriteParts tail l ltac:(fun bytes ending =>

     change (fieldImage (take k l ++ bytes ++ drop ending l) off field);
     replace ending with (k+length bytes)%nat by decodeItemExitImageArithmetic;
     first [lazymatch field with [ ?value ] =>
              decodeItemExitLiteralField l bytes k off value end
       | assert (Heq : bytes=field) by
              first [reflexivity | rewrite <- decodeItemStoredWordBytes; reflexivity];
            try rewrite <- Heq; apply decodeItemExitWriteField; [decodeItemExitImageArithmetic|reflexivity]
       | eapply decodeItemExitWriteFieldKeep; [decodeItemExitImageArithmetic|reflexivity|
           first [left; decodeItemExitImageArithmetic|right; decodeItemExitImageArithmetic]|decodeItemExitImageSolve]])
 | |- preservedImage ?before (take ?k ?l ++ ?tail) ?off ?count =>
   decodeItemExitWriteParts tail l ltac:(fun bytes ending =>

     change (preservedImage before (take k l ++ bytes ++ drop ending l) off count);
     replace ending with (k+length bytes)%nat by decodeItemExitImageArithmetic;
     eapply decodeItemExitWritePreserved; [decodeItemExitImageArithmetic|reflexivity|
       first [left; decodeItemExitImageArithmetic|right; decodeItemExitImageArithmetic]|decodeItemExitImageSolve])
 | |- preservedImage ?before ?before _ _ => unfold preservedImage; intros; reflexivity
 | |- fieldImage (<[?i:=?value]> ?l) _ _ =>
   rewrite insert_take_drop; [decodeItemExitImageSolve|decodeItemExitImageArithmetic]
 | |- preservedImage _ (<[?i:=?value]> ?l) _ _ =>
   rewrite insert_take_drop; [decodeItemExitImageSolve|decodeItemExitImageArithmetic]
 end].
#[export] Hint Extern 0 (SimplAnd (fieldImage ?after ?off ?field) True) =>
 unfold SimplAnd; split; [intros _; decodeItemExitImageSolve|intros _; exact I] : typeclass_instances.
#[export] Hint Extern 0 (SimplAnd (preservedImage ?before ?after ?off ?count) True) =>
 unfold SimplAnd; split; [intros _; decodeItemExitImageSolve|intros _; exact I] : typeclass_instances.

Open Scope Z_scope.
Ltac decodeItemExitPayloadPointer args :=
 unfold itemPayloadPointer;
 match goal with Hhead : decodeItemInputHead args ?prefix ?rest |- _ =>
  change (decodeItemInputBytes args = prefix :: rest) in Hhead;
  rewrite Hhead;
  first [assert (Hx15eq : (bv_unsigned prefix =? 128)%Z = false) by
           (apply Z.eqb_neq; lia); rewrite Hx15eq
        |assert (Hx15eq : (bv_unsigned prefix =? 128)%Z = true) by
           (apply Z.eqb_eq; lia); rewrite Hx15eq]
 end.
Ltac decodeItemExitDecodeField after off bytes :=
 let Hstore := fresh "Hx15store" in
 let Hslice := fresh "Hx15slice" in
 assert (Hstore : fieldImage after off bytes) by decodeItemExitImageSolve;
 pose proof (fieldImage_slice after bytes off Hstore) as Hslice;
 assert (Hx15length : length bytes = 8%nat) by
   first [assumption|unfold word64Bytes; rewrite map_length; rewrite seq_length; reflexivity];
 rewrite Hx15length in Hslice; rewrite Hslice;
 first [assumption | rewrite <- decodeItemStoredWordBytes;
   rewrite decodeItemStoredWordValue;
   first [assumption | match goal with args : DecodeItemArgs |- _ =>
     try decodeItemExitPayloadPointer args;
     first [assumption | match goal with Hreg : bv_unsigned ?r = ?v |- bv_unsigned ?r = _ => rewrite Hreg end;
       first [reflexivity | symmetry; apply Z.mod_small; unfold word64Modulus; lia]] end]].
Ltac decodeItemExitDecoder after off value :=
 first [multimatch goal with Hreg : bv_unsigned ?r = _ |- _ =>
    decodeItemExitDecodeField after off constr:(word64Bytes (bv_unsigned r)) end
 |multimatch goal with Hfield : fieldImage ?original off ?bytes |- _ =>
    decodeItemExitDecodeField after off bytes end].
Ltac decodeItemExitImageLeaf :=
 first [assumption | reflexivity | apply decodeItemSliceField |
   solve [symmetry; apply preservedImage_slice; decodeItemExitImageSolve] |
   decodeItemExitImageArithmetic | decodeItemExitImageSolve |
   lazymatch goal with
   | |- fieldImage ?after ?offset [?value] =>
     multimatch goal with Hfield : fieldImage ?before 32%nat [?first; ?second] |- _ =>
      first [unify offset 32%nat; unify value first;
       assert (Hx15single : fieldImage before 32%nat [first]) by
         (intros i Hi; destruct i; [exact (Hfield 0%nat ltac:(cbn; lia))|cbn in Hi; lia]);
       decodeItemExitImageSolve
      |unify offset 33%nat; unify value second;
       assert (Hx15single : fieldImage before 33%nat [second]) by
         (intros i Hi; destruct i; [exact (Hfield 1%nat ltac:(cbn; lia))|cbn in Hi; lia]);
       decodeItemExitImageSolve]
     end
   | |- littleEndian (take 8%nat (drop ?off ?after)) = ?value => decodeItemExitDecoder after off value
   | |- littleEndian (take 8%nat ?after) = ?value =>
     change (littleEndian (take 8%nat (drop 0%nat after)) = value);
     decodeItemExitDecoder after constr:(0%nat) value
   end].
Ltac decodeItemExitSuccessImage :=
 lazymatch goal with |- ?P =>
  lazymatch P with successResult40 _ _ _ _ _ _ => idtac end;
  let evidence := constr:(_ : SimplAnd P _) in
  apply (proj1 (@simpl_and _ _ evidence))
 end;
 repeat split; solve [decodeItemExitImageLeaf].
Ltac decodeItemExitStorageLink :=
 repeat match goal with
 | Hlink : returnStorage ?locals = decodeItemBeforeStorage ?args |- _ =>
   lazymatch goal with |- context[returnStorage locals] =>
    match goal with Hlength : length (returnStorage locals) = 40%nat |- _ =>
     let Hbefore := fresh "HbeforeLength" in
     pose proof Hlength as Hbefore; rewrite Hlink in Hbefore
    end;
    rewrite Hlink
   end
 end.

Ltac decodeItemExitShortListFacts args :=
 multimatch goal with
 | Hhead : decodeItemInputHead args ?prefix ?rest,
   locals : DecodeItemReturnLocals |- _ =>
   zesu_saturate_derived_facts;
   let Hfacts := fresh "HshortListOutputFacts" in
   assert (Hfacts : decodeItemShortListOutputFacts args locals prefix rest) by
     (unfold decodeItemShortListOutputFacts; repeat first [assumption | split]);
   zesu_saturate_derived_facts;
   match goal with
   | Hplus : bv_unsigned ((returnA1 locals + 1)%bv) = (decodeItemInputPointer args + 1)%Z /\
       bv_unsigned ((returnA3 locals + 1)%bv) = (1 + (bv_unsigned prefix - 192))%Z |- _ =>
       destruct Hplus
   end;
   zesu_split_folded_pure
 end.

Ltac decodeItemExitMeaning :=
 repeat match goal with |- context [(?base + ?offset - ?base)%Z] =>
   replace (base+offset-base)%Z with offset by lia end;
 first [assumption |
 lazymatch goal with |- DecodeMeaningModuloKnownBugs ?args ?after =>
  first [match goal with locals : DecodeItemReturnLocals |- _ =>
    change (DecodeMeaningModuloKnownBugs args (decodeItemEmptyStringUpdatedImage locals));
    match goal with Hhead : decodeItemInputHead args ?prefix ?rest |- _ =>
      apply (decodeItemEmptyStringUpdatedMeaning args locals prefix rest) end;
    unfold decodeItemEmptyStringOutputFacts;
    repeat lazymatch goal with |- _ /\ _ => split end; assumption end |
  first [multimatch goal with
   Hmeaning : forall img, (exists pad17 pad34, _) -> DecodeMeaningModuloKnownBugs args img |- _ =>
    try decodeItemExitShortListFacts args;
    decodeItemExitStorageLink;
    lazymatch goal with |- DecodeMeaningModuloKnownBugs args ?normalized =>
      eapply (Hmeaning normalized) end;
    exists (take 7%nat (drop 17%nat (decodeItemBeforeStorage args))),
           (take 6%nat (drop 34%nat (decodeItemBeforeStorage args)));
    repeat lazymatch goal with |- _ /\ _ => split end; solve [decodeItemExitSuccessImage | decodeItemExitImageLeaf]
   end
  |multimatch goal with
   Hmeaning : forall img, errorResult40 img -> img = errorEncoding -> DecodeMeaningModuloKnownBugs args img |- _ =>
    let Heq := fresh "Hx15error" in
    assert (Heq : after = errorEncoding) by
     (let before := fresh "before" in
      let Hlength' := fresh "Hlength" in
      match goal with Hlength : length ?storage = 40%nat |- _ =>
       lazymatch goal with |- context[storage] => idtac end;
       generalize Hlength; generalize storage; intros before Hlength'
      end;
      do 40 (destruct before as [|? before]; [discriminate|]);
      destruct before; [unfold errorEncoding;
       cbn [Z_to_bv N.to_nat take drop firstn skipn list_fmap fmap]; reflexivity
       |cbn in Hlength'; lia]);
    apply (Hmeaning after); [rewrite Heq; exact (proj1 errorReturnImage)|exact Heq]
   end]]
 end].
#[export] Hint Extern 0 (SimplAnd (DecodeMeaningModuloKnownBugs ?args ?after) True) =>
 unfold SimplAnd; split; [intros _; solve [decodeItemExitMeaning]|intros _; exact I] : typeclass_instances.

Open Scope Z_scope.

Lemma decodeItemExitEpilogueZero (args : DecodeItemArgs) (frame : list byte) :
  decodeItemSavedFrameFacts args frame ->
  (RlpDecodeItem.decodeItemStackBytes - Z.of_nat (length frame) = 0)%Z.
Proof. intros [Hlength _]. rewrite Hlength. reflexivity. Qed.
#[export] Hint Extern 0 (ZesuRegionBounds ?P) =>
  lazymatch P with
  | (?size - Z.of_nat (length ?frame) = 0)%Z =>
    match goal with Hframe : decodeItemSavedFrameFacts ?args frame |- _ =>
      change P; exact (decodeItemExitEpilogueZero args frame Hframe)
    end
  end : typeclass_instances.

#[export] Hint Extern 4 (SimplImpl _ _) =>
  unLET;
  lazymatch goal with
  | |- SimplImpl ?condition ?result =>
    lazymatch condition with
    | context[Z_to_bv 64 (little_endian_to_bv 8 _)] =>
      match goal with
      | Hframe : decodeItemSavedFrameFacts ?capturedArgs ?capturedFrame |- _ =>
        let Hdecoder := fresh "HfaultDecoderForRule" in
        pose proof (decodeItemSavedReturnDecoder capturedArgs capturedFrame Hframe) as Hdecoder;
        repeat match type of Hdecoder with
        | context[Z.to_nat (?base + ?offset - ?base)] =>
          replace (base + offset - base)%Z with offset in Hdecoder by lia
        end;
        cbn [N.to_nat Z.to_nat] in Hdecoder;
        progress rewrite Hdecoder;
        typeclasses eauto
      end
    end
  end : typeclass_instances.
