(* Switches the refusal diagnostics on (see Diagnostics.v). Import this module
   after ZesuSsz.Automation2.All, in a diagnostic copy of a block caller only.
   No production module imports it. The instance is exported, so it is active
   only where this module is imported. *)
Require Export ZesuSsz.Automation2.Diagnostics.

#[export] Instance zesu_diagnostics_enabled : ZesuDiagnosticsOn := I.
