Require Export ZesuSsz.Automation2.AdjacentWordCodecHints282.
Require Import isla.riscv64.riscv64.
Require Import stdpp.bitvector.definitions.
From lithium Require Import instances.
From iris.algebra Require Import dfrac.
From Coq Require Import List NArith ZArith.
Import ListNotations.
Set Default Proof Mode "Classic".

Section scalar_identity.
  Context `{!islaG Sigma}.
  Lemma subsume_fraction_scalar285 A (base : Z) (q : dfrac) (width : N)
      (word : bv width) (value : A -> bv width) (G : A -> iProp Sigma) :
    (∃ x, ⌜word = value x⌝ ∗ G x)%I
    ⊢ subsume (base ↦ₘ{q} word) (fun x : A => base ↦ₘ{q} value x) G.
  Proof.
    iDestruct 1 as (x ->) "HG".
    iIntros "Hword". iExists x. iFrame.
  Qed.
  Definition subsume_fraction_scalar285_inst := [instance subsume_fraction_scalar285].
End scalar_identity.

#[export] Hint Extern 90
  (Subsume (mem_mapsto ?base ?q ?word)
    (fun x : ?A => mem_mapsto ?base ?q (?value x))) =>
    lazymatch q with
    | DfracOwn 1%Qp => fail 1 "The stock rule handles full ownership."
    | _ => idtac
    end;
    tryif has_evar q then fail 1 "The fraction contains an evar." else idtac;
    let word_type := type of word in
    lazymatch word_type with
    | bv ?width => apply (subsume_fraction_scalar285_inst A base q width word value)
    end
  : typeclass_instances.

#[export] Hint Extern 90
  (RelatedTo (fun x : ?A => mem_mapsto ?base ?q (?value x))) =>
    lazymatch q with
    | DfracOwn 1%Qp => fail 1 "The stock finder handles full ownership."
    | _ => idtac
    end;
    tryif has_evar q then fail 1 "The fraction contains an evar." else idtac;
    let value_type := type of value in
    lazymatch value_type with
    | _ -> bv ?width =>
        tryif has_evar width then fail 1 "The word width contains an evar." else idtac;
        tryif is_closed_term width then idtac else fail 1 "The word width is symbolic.";
        let permitted := eval vm_compute in
          (N.ltb 0 width && N.eqb (width mod 8) 0)%bool in
        lazymatch permitted with
        | true => refine {| rt_fic := FindDirect (fun word : bv width => (base ↦ₘ{q} word)%I) |}
        | false => fail 1 "The word must contain positive whole bytes."
        end
    end
  : typeclass_instances.

#[export] Hint Extern 90
  (RelatedTo (fun _ : ?A => mem_mapsto_array ?base ?q ?bytes)) =>
    lazymatch q with
    | DfracOwn 1%Qp => fail 1 "The stock finder handles full ownership."
    | _ => idtac
    end;
    tryif has_evar q then fail 1 "The fraction contains an evar." else idtac;
    tryif has_evar bytes then fail 1 "The target bytes contain an evar." else idtac;
    lazymatch bytes with
    | bv_extract 0 8 ?low :: _ =>
        adjacent_word_counts low bytes ltac:(fun n m =>
          let width := eval vm_compute in (8 * N.of_nat n)%N in
          refine {| rt_fic := FindDirect (fun word : bv width => (base ↦ₘ{q} word)%I) |})
    end
  : typeclass_instances.
