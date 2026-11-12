(* The frozen core declares these instances `Global`, so each stays active
   wherever its frozen module is loaded, beside the Automation2 copy at the
   same priority. Every failing instance search then runs the same rule
   twice. The Automation2 copies stay; the frozen copies are removed here,
   for every file that loads this core. Frozen proofs that do not load this
   core keep them. A library instance that both cores register again
   (`subsume_instr_some_pre_inst`) is one hint and stays. *)
Require ZesuSsz.Automation.UninitRegions.
Require ZesuSsz.Automation.ByteArrays.
Require ZesuSsz.Automation.InstrPre.
Require ZesuSsz.Automation.Rewrites.

Global Remove Hints
  ZesuSsz.Automation.UninitRegions.find_mem_region_inst
  ZesuSsz.Automation.UninitRegions.subsume_uninit_region_inst
  ZesuSsz.Automation.UninitRegions.subsume_uninit_region_crossing_inst
  ZesuSsz.Automation.UninitRegions.simplify_uninit_empty_hyp_inst
  ZesuSsz.Automation.UninitRegions.simplify_uninit_empty_goal_inst
  ZesuSsz.Automation.UninitRegions.subsume_mem_word_address_inst
  ZesuSsz.Automation.ByteArrays.subsume_mem_byte_array_8_uninit_inst
  ZesuSsz.Automation.ByteArrays.subsume_mem_byte_array_uninit_inst
  ZesuSsz.Automation.ByteArrays.subsume_mem_scratch_byte_array_1_uninit_inst
  ZesuSsz.Automation.ByteArrays.subsume_mem_optional_object_array_inst
  ZesuSsz.Automation.ByteArrays.subsume_mem_word_byte_array_inst
  ZesuSsz.Automation.ByteArrays.subsume_mem_byte_singleton_inst
  ZesuSsz.Automation.InstrPre.subsume_instr_pre_zesu_inst
  ZesuSsz.Automation.Rewrites.zesu_integer_array_word_inhabited
  : typeclass_instances.
