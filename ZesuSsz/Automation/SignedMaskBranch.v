From stdpp Require Import tactics bitvector.definitions.
Require Import ZesuSsz.Automation.SwitchDispatch.

Class ZesuStepSignedMaskBranch : Prop := {}.

(* Transport retained branch evidence across an exact whole-word equality.
   Only closed masks, closed bounds, and strictly widening widths qualify. *)
Ltac zesu_signed_mask_branch :=
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuStepSignedMaskBranch);
  let target := match goal with |- ?target => target end in
  let relation := lazymatch target with
                  | ~ ?relation => relation
                  | _ => target
                  end in
  lazymatch relation with
  | Z.ge (@bv_signed ?wide (@bv_zero_extend ?width ?wide
              (@bv_and ?width ?payload ?mask))) (@bv_signed ?wide ?bound) =>
      is_closed_term width;
      is_closed_term wide;
      is_closed_term mask;
      is_closed_term bound;
      let widening := eval cbv in (N.ltb width wide) in
      lazymatch widening with true => idtac | _ => fail 0 end;
      match goal with
      | Hlink : @bv_and width payload mask = ?view |- _ =>
          solve [rewrite Hlink; assumption]
      | Hlink : ?view = @bv_and width payload mask |- _ =>
          solve [rewrite <- Hlink; assumption]
      end
  end.
