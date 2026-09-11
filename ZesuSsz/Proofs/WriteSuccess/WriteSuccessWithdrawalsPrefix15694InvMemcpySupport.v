Require Import ZesuSsz.Automation.All.
From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.opsem.

Open Scope Z_scope.

Lemma writeSuccessReadMemListBacked memory address length bytes :
  read_mem_list memory address (N.of_nat length) = Some bytes ->
  forall location,
    address <= location < address + Z.of_nat length ->
    is_Some (memory !! Z_to_bv 64 location).
Proof.
  revert address bytes.
  induction length as [|length IH]; intros address bytes Hread location Hlocation.
  - cbn in Hlocation. lia.
  - unfold read_mem_list in Hread. rewrite seqZ_cons in Hread; last lia.
    cbn in Hread.
    destruct (Z_to_bv_checked 64 address) as [addressBits|] eqn:Haddress;
      cbn in Hread; last discriminate.
    destruct (memory !! addressBits) as [byte|] eqn:Hbyte;
      cbn in Hread; last discriminate.
    destruct (mapM (M := option)
      (fun x : Z => Z_to_bv_checked 64 x ≫= (memory !!.))
      (seqZ (Z.succ address) (Z.pred (Z.of_N (N.of_nat (S length))))))
      as [tail|] eqn:Htail; cbn in Hread; last discriminate.
    inversion Hread; subst bytes.
    destruct (Z.eq_dec location address) as [->|Hdifferent].
    + apply Z_to_bv_checked_Some in Haddress.
      rewrite Haddress.
      rewrite Z_to_bv_bv_unsigned. exists byte. exact Hbyte.
    + apply (IH (address + 1) tail).
      * unfold read_mem_list.
        replace (Z.of_N (N.of_nat length)) with
          (Z.pred (Z.of_N (N.of_nat (S length)))) by lia.
        replace (address + 1) with (Z.succ address) by lia.
        exact Htail.
      * cbn in Hlocation. lia.
Qed.

Print Assumptions writeSuccessReadMemListBacked.
