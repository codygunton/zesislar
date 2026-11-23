(* Switches the spatial leftover export on (see SpatialExport.v). A spatial
   export run is a residual export run, so this module also switches the
   residual export on. Import it after ZesuSsz.Automation2.All, in an export
   copy of a block caller only. No production module imports it. The
   instance is exported, so it is active only where this module is imported. *)
Require Export ZesuSsz.Automation2.ResidualExportOn.
Require Export ZesuSsz.Automation2.SpatialExport.

#[export] Instance zesu_spatial_export_enabled : ZesuSpatialExportOn := I.
