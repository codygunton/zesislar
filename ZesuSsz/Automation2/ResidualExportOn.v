(* Switches the residual export on (see Diagnostics.v and ResidualExport.v).
   Import this module after ZesuSsz.Automation2.All, in an export copy of a
   block caller only (tools/block/residual_loop.py writes that copy). No
   production module imports it. The instance is exported, so it is active
   only where this module is imported. *)
Require Export ZesuSsz.Automation2.Diagnostics.

#[export] Instance zesu_residual_export_enabled : ZesuResidualExportOn := I.
