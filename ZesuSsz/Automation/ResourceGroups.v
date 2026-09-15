Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
From iris.proofmode Require Import environments.

(* Pure extraction removes its persistent source. Separation keeps both children. *)
Ltac zesu_expose_environment_alias :=
  repeat match goal with
  | Hlocal := _ : envs (iPropI _) |- envs_entails ?current _ =>
      constr_eq Hlocal current; subst Hlocal
  end.

Ltac zesu_open_resource_groups :=
  repeat iMatchHyp ltac:(fun H body =>
    lazymatch body with
    | (_ ∗ _)%I => iDestruct H as "[? ?]"
    | (⌜_⌝)%I => iDestruct H as %?; try iClear H
    end).

(* Split an instruction bundle only when its first PC is requested. *)
Ltac zesu_open_requested_instr_bundle :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindInstrKind ?address _) _) =>
      iMatchHyp ltac:(fun H body =>
        lazymatch body with
        | (instr ?firstAddress _ ∗ _)%I =>
            constr_eq firstAddress address;
            iDestruct H as "[? ?]"
        end)
  end.

(* Unfold only a package whose first resource is the current goal resource. *)
Ltac zesu_open_matching_resource_package :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (?requested ∗ _)%I =>
      iMatchHyp ltac:(fun H body =>
        let head := get_head body in
        tryif first [constr_eq head constr:(@bi_sep) |
                     constr_eq head constr:(@bi_pure)] then fail else
          let expanded := eval cbv beta delta [head] in body in
          lazymatch expanded with
          | (?first ∗ _)%I =>
              constr_eq first requested;
              progress iEval (unfold head) in H;
              iDestruct H as "[? ?]"
          end)
  end.

(* Open a let-bound copied-word package only for its requested first word. *)
Ltac zesu_open_matching_copied_word_package :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ ((?address ↦ₘ ?value)%I ∗ _)%I =>
      iMatchHyp ltac:(fun H body =>
        let head := get_head body in
        tryif first [constr_eq head constr:(@bi_sep) |
                     constr_eq head constr:(@bi_pure)] then fail else
          let symbolic := eval cbv beta delta [head] in body in
          lazymatch symbolic with
          | let words := ?tailWords in ?resources =>
              let expanded := eval cbv beta zeta delta [head] in body in
              lazymatch expanded with
              | (?first ∗ _)%I =>
                  constr_eq first constr:((address ↦ₘ value)%I);
                  progress iEval (unfold head) in H;
                  iDestruct H as "[? ?]"
              end
          end)
  end.

(* Open a two-array package only when its first full array is requested. *)
Ltac zesu_open_requested_exact_array_pair :=
  lazymatch goal with
  | |- envs_entails _ ((?address ↦ₘ∗ ?bytes)%I ∗ _)%I =>
      zesu_expose_environment_alias;
      iSelect ((address ↦ₘ∗ bytes) ∗ (_ ↦ₘ∗ _))%I
        ltac:(fun H => iDestruct H as "[? ?]")
  end.

(* Open an exact array-and-pure package as one requested resource. *)
Ltac zesu_open_matching_array_pure_bundle :=
  lazymatch goal with
  | |- envs_entails _ ((?array ∗ ⌜?requested⌝)%I ∗ _)%I =>
      lazymatch array with
      | (_ ↦ₘ∗ _)%I =>
          zesu_expose_environment_alias;
          iMatchHyp ltac:(fun H body =>
            let head := get_head body in
            tryif first [constr_eq head constr:(@bi_sep) |
                         constr_eq head constr:(@bi_pure)] then fail else
              let expanded := eval cbv beta zeta delta [head] in body in
              constr_eq expanded constr:((array ∗ ⌜requested⌝)%I);
              progress iEval (unfold head) in H;
              iDestruct H as "[? ?]";
              zesu_open_resource_groups)
      end
  end.

(* Open only the first full array inside a nested resource package. *)
Ltac zesu_open_requested_nested_array_package :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ ((?address ↦ₘ∗ ?bytes)%I ∗ _)%I =>
      let requested := constr:((address ↦ₘ∗ bytes)%I) in
      iMatchHyp ltac:(fun H body =>
        let outerHead := get_head body in
        let outer := eval cbv beta zeta delta [outerHead] in body in
        lazymatch outer with
        | (?inner ∗ _)%I =>
            let innerHead := get_head inner in
            let innerBody := eval cbv beta zeta delta [innerHead] in inner in
            lazymatch innerBody with
            | (?first ∗ ⌜_⌝)%I =>
                constr_eq first requested;
                progress iEval (unfold outerHead) in H;
                iDestruct H as "[? ?]";
                iMatchHyp ltac:(fun Hinner current =>
                  let currentHead := get_head current in
                  constr_eq currentHead innerHead;
                  progress iEval (unfold innerHead) in Hinner;
                  iDestruct Hinner as "[? ?]")
            end
        end)
  end.

(* Expose the machine collection only for the mstatus field request. *)
Ltac zesu_open_requested_struct_sys_package :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _
      (find_in_context (FindStructRegMapsTo "mstatus" "bits") _) =>
      iMatchHyp ltac:(fun H body =>
        let outerHead := get_head body in
        tryif first [constr_eq outerHead constr:(@bi_sep) |
                     constr_eq outerHead constr:(@bi_pure)] then fail else
          let outer := eval cbv beta zeta delta [outerHead] in body in
          lazymatch outer with
          | (?inner ∗ _)%I =>
              let innerHead := get_head inner in
              let innerBody := eval cbv beta zeta delta [innerHead] in inner in
              lazymatch innerBody with
              | (reg_col ?shape ∗ _)%I =>
                  constr_eq shape constr:(zesu_sys_regs);
                  progress iEval (unfold outerHead) in H;
                  iDestruct H as "[? ?]";
                  iMatchHyp ltac:(fun Hinner current =>
                    let currentHead := get_head current in
                    constr_eq currentHead innerHead;
                    progress iEval (unfold innerHead) in Hinner;
                    iDestruct Hinner as "[? ?]")
              end
          end)
  end.

(* Branch frames preserve x9 behind their transparent common frame. *)
Ltac zesu_open_requested_saved_x9_package :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindRegMapsTo "x9") _) =>
      iMatchHyp ltac:(fun H body =>
        let outerHead := get_head body in
        tryif first [constr_eq outerHead constr:(@bi_sep) |
                     constr_eq outerHead constr:(@bi_pure)] then fail else
          let outer := eval cbv beta zeta delta [outerHead] in body in
          let innerHead := get_head outer in
          let inner := eval cbv beta zeta delta [innerHead] in outer in
          lazymatch inner with
          | (reg_col ?other ∗ reg_col ?saved ∗ reg_col ?global ∗
              "x8" ↦ᵣ RVal_Bits ?old8 ∗ "x9" ↦ᵣ RVal_Bits ?old9 ∗ _)%I =>
              constr_eq global constr:(
                [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)]);
              progress iEval (unfold outerHead) in H;
              progress iEval (unfold innerHead) in H;
              iDestruct H as "[? ?]";
              zesu_open_resource_groups
          end)
  end.

(* Match the requested first frame resource through two transparent heads. *)
Ltac zesu_open_matching_two_level_frame :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (?requested ∗ _)%I =>
      lazymatch requested with
      | reg_col _ =>
      iMatchHyp ltac:(fun H body =>
        let outerHead := get_head body in
        tryif first [constr_eq outerHead constr:(@bi_sep) |
                     constr_eq outerHead constr:(@bi_pure)] then fail else
          let outer := eval cbv beta zeta delta [outerHead] in body in
          let innerHead := get_head outer in
          tryif first [constr_eq innerHead constr:(@bi_sep) |
                       constr_eq innerHead constr:(@bi_pure)] then fail else
            let inner := eval cbv beta zeta delta [innerHead] in outer in
            lazymatch inner with
            | (?first ∗ _)%I =>
                constr_eq first requested;
                progress iEval (unfold outerHead) in H;
                progress iEval (unfold innerHead) in H;
                iDestruct H as "[? ?]"
            end)
      end
  end.

Ltac zesu_is_pure_resource body :=
  lazymatch body with
  | (bi_pure _)%I => idtac
  | (?left ∗ ?right)%I =>
      zesu_is_pure_resource left; zesu_is_pure_resource right
  end.

(* Take an exact pure descriptor fact while retaining its array owner. *)
Ltac zesu_extract_descriptor_pure requested :=
  iMatchHyp ltac:(fun H body =>
    let head := get_head body in
    tryif first [constr_eq head constr:(@bi_sep) |
                 constr_eq head constr:(@bi_pure)] then fail else
      let unfolded := eval cbv beta zeta delta [head] in body in
      lazymatch unfolded with
      | (?array ∗ ⌜?actual⌝)%I =>
          lazymatch array with
          | (_ ↦ₘ∗ _)%I =>
              constr_eq actual requested;
              progress iEval (unfold head) in H;
              iDestruct H as "[? ?]";
              zesu_open_resource_groups
          end
      end).

Ltac zesu_extract_matching_descriptor_pure :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (⌜?requested⌝)%I =>
      zesu_extract_descriptor_pure requested
  | |- envs_entails _ (⌜?requested⌝ ∗ _)%I =>
      zesu_extract_descriptor_pure requested
  end.

Ltac zesu_promote_folded_pure_resources :=
  repeat iMatchHyp ltac:(fun H body =>
    let head := get_head body in
    tryif first [constr_eq head constr:(@bi_pure) |
                 constr_eq head constr:(@bi_sep)] then fail else
      let expanded := eval cbv beta delta [head] in body in
      zesu_is_pure_resource expanded;
      progress iEval (unfold head) in H;
      zesu_open_resource_groups).

Ltac zesu_finish_pure_resources :=
  lazymatch goal with
  | |- envs_entails _ ?body =>
      zesu_is_pure_resource body;
      solve [repeat first
        [solve [iPureIntro; assumption] | solve [done] | iSplit |
         solve [iPureIntro; first [lia | bv_solve]]]]
  end.
