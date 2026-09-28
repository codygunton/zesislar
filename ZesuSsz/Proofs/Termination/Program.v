Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
From stdpp Require Import gmap.
Require Import isla.riscv64.riscv64.
From IslaTraces.main Require Import instrs.
From IslaTraces.read_input Require Import instrs.
From IslaTraces.allocator_get Require Import instrs.
From IslaTraces.write_failure Require Import instrs.
From IslaTraces.zkvm_exit Require Import instrs.
From IslaTraces.write_success_00 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
From IslaTraces.write_success_02 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_05 Require Import instrs.
From IslaTraces.write_success_06 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_08 Require Import instrs.
From IslaTraces.write_success_09 Require Import instrs.
From IslaTraces.write_success_10 Require Import instrs.
From IslaTraces.write_success_11 Require Import instrs.
From IslaTraces.write_success_12 Require Import instrs.
From IslaTraces.write_success_13 Require Import instrs.
From IslaTraces.write_success_14 Require Import instrs.
From IslaTraces.write_success_15 Require Import instrs.
From IslaTraces.write_success_16 Require Import instrs.
From IslaTraces.write_success_17 Require Import instrs.
From IslaTraces.write_success_18 Require Import instrs.
From IslaTraces.write_success_19 Require Import instrs.
From IslaTraces.write_success_20 Require Import instrs.
From IslaTraces.write_success_21 Require Import instrs.
From IslaTraces.write_success_22 Require Import instrs.
From IslaTraces.write_success_23 Require Import instrs.
From IslaTraces.write_success_24 Require Import instrs.
From IslaTraces.write_success_25 Require Import instrs.
From IslaTraces.write_success_26 Require Import instrs.
From IslaTraces.write_success_27 Require Import instrs.
From IslaTraces.write_success_28 Require Import instrs.
From IslaTraces.write_success_29 Require Import instrs.
From IslaTraces.write_success_30 Require Import instrs.
From IslaTraces.write_success_31 Require Import instrs.
From IslaTraces.write_success_32 Require Import instrs.
From IslaTraces.write_success_33 Require Import instrs.
From IslaTraces.write_success_34 Require Import instrs.
From IslaTraces.write_success_35 Require Import instrs.
From IslaTraces.write_success_36 Require Import instrs.
From IslaTraces.write_success_37 Require Import instrs.
From IslaTraces.write_success_38 Require Import instrs.
From IslaTraces.write_success_39 Require Import instrs.
From IslaTraces.write_success_40 Require Import instrs.
From IslaTraces.write_success_41 Require Import instrs.
From IslaTraces.write_success_42 Require Import instrs.
From IslaTraces.write_success_43 Require Import instrs.
From IslaTraces.write_success_44 Require Import instrs.
From IslaTraces.write_success_45 Require Import instrs.
From IslaTraces.write_success_46 Require Import instrs.
From IslaTraces.write_success_47 Require Import instrs.
From IslaTraces.write_success_48 Require Import instrs.
From IslaTraces.write_success_49 Require Import instrs.
From IslaTraces.write_success_50 Require Import instrs.
From IslaTraces.write_success_51 Require Import instrs.
From IslaTraces.write_success_52 Require Import instrs.
From IslaTraces.write_success_53 Require Import instrs.
From IslaTraces.write_success_54 Require Import instrs.
From IslaTraces.write_success_55 Require Import instrs.
From IslaTraces.write_success_56 Require Import instrs.
From IslaTraces.write_success_57 Require Import instrs.
From IslaTraces.write_success_58 Require Import instrs.
From IslaTraces.write_success_59 Require Import instrs.
From IslaTraces.write_success_60 Require Import instrs.
From IslaTraces.write_success_61 Require Import instrs.
From IslaTraces.write_success_62 Require Import instrs.
From IslaTraces.write_success_63 Require Import instrs.
From IslaTraces.write_success_64 Require Import instrs.
From IslaTraces.write_success_65 Require Import instrs.
From IslaTraces.write_success_66 Require Import instrs.
From IslaTraces.write_success_67 Require Import instrs.
From IslaTraces.write_success_68 Require Import instrs.
From IslaTraces.write_success_69 Require Import instrs.
From IslaTraces.write_success_70 Require Import instrs.
From IslaTraces.write_success_71 Require Import instrs.
From IslaTraces.write_success_72 Require Import instrs.
From IslaTraces.write_success_73 Require Import instrs.
From IslaTraces.write_success_74 Require Import instrs.
From IslaTraces.write_success_75 Require Import instrs.
From IslaTraces.write_success_76 Require Import instrs.
From IslaTraces.write_success_77 Require Import instrs.
From IslaTraces.write_success_78 Require Import instrs.
From IslaTraces.write_success_79 Require Import instrs.
From IslaTraces.write_success_80 Require Import instrs.
From IslaTraces.write_success_81 Require Import instrs.
From IslaTraces.write_success_82 Require Import instrs.
From IslaTraces.write_success_83 Require Import instrs.
From IslaTraces.write_success_84 Require Import instrs.
From IslaTraces.write_success_85 Require Import instrs.
From IslaTraces.write_success_86 Require Import instrs.
From IslaTraces.write_success_87 Require Import instrs.
From IslaTraces.write_success_88 Require Import instrs.
From IslaTraces.write_success_89 Require Import instrs.
From IslaTraces.write_success_90 Require Import instrs.
From IslaTraces.write_success_91 Require Import instrs.
From IslaTraces.write_success_92 Require Import instrs.
From IslaTraces.write_success_93 Require Import instrs.
From IslaTraces.write_success_94 Require Import instrs.
From IslaTraces.write_success_95 Require Import instrs.
From IslaTraces.write_success_96 Require Import instrs.
From IslaTraces.write_success_97 Require Import instrs.
From IslaTraces.write_success_98 Require Import instrs.
From IslaTraces.write_success_99 Require Import instrs.
From IslaTraces.write_success_100 Require Import instrs.
From IslaTraces.write_success_101 Require Import instrs.
From IslaTraces.write_success_102 Require Import instrs.
From IslaTraces.write_success_103 Require Import instrs.
From IslaTraces.write_success_104 Require Import instrs.
From IslaTraces.write_success_105 Require Import instrs.
From IslaTraces.write_success_106 Require Import instrs.
From IslaTraces.write_success_107 Require Import instrs.
From IslaTraces.write_success_108 Require Import instrs.
From IslaTraces.write_success_109 Require Import instrs.
From IslaTraces.write_success_110 Require Import instrs.
From IslaTraces.write_success_111 Require Import instrs.
From IslaTraces.write_success_112 Require Import instrs.
From IslaTraces.write_success_113 Require Import instrs.
From IslaTraces.write_success_114 Require Import instrs.
From IslaTraces.write_success_115 Require Import instrs.
From IslaTraces.write_success_116 Require Import instrs.
From IslaTraces.write_success_117 Require Import instrs.
From IslaTraces.write_success_118 Require Import instrs.
From IslaTraces.write_success_119 Require Import instrs.
From IslaTraces.write_success_120 Require Import instrs.
From IslaTraces.write_success_121 Require Import instrs.
From IslaTraces.write_success_122 Require Import instrs.
From IslaTraces.write_success_123 Require Import instrs.
From IslaTraces.write_success_124 Require Import instrs.
From IslaTraces.write_success_125 Require Import instrs.
From IslaTraces.write_success_126 Require Import instrs.
From IslaTraces.write_success_127 Require Import instrs.

Import ListNotations.

Definition zesuTerminationProgramEntriesZ : list (Z * isla_trace) :=
  IslaTraces.main.instrs.instr_map ++
  IslaTraces.read_input.instrs.instr_map ++
  IslaTraces.allocator_get.instrs.instr_map ++
  firstn 5 IslaTraces.write_failure.instrs.instr_map ++
  IslaTraces.zkvm_exit.instrs.instr_map ++
  IslaTraces.write_success_00.instrs.instr_map ++
  IslaTraces.write_success_01.instrs.instr_map ++
  IslaTraces.write_success_02.instrs.instr_map ++
  IslaTraces.write_success_03.instrs.instr_map ++
  IslaTraces.write_success_04.instrs.instr_map ++
  IslaTraces.write_success_05.instrs.instr_map ++
  IslaTraces.write_success_06.instrs.instr_map ++
  IslaTraces.write_success_07.instrs.instr_map ++
  IslaTraces.write_success_08.instrs.instr_map ++
  IslaTraces.write_success_09.instrs.instr_map ++
  IslaTraces.write_success_10.instrs.instr_map ++
  IslaTraces.write_success_11.instrs.instr_map ++
  IslaTraces.write_success_12.instrs.instr_map ++
  IslaTraces.write_success_13.instrs.instr_map ++
  IslaTraces.write_success_14.instrs.instr_map ++
  IslaTraces.write_success_15.instrs.instr_map ++
  IslaTraces.write_success_16.instrs.instr_map ++
  IslaTraces.write_success_17.instrs.instr_map ++
  IslaTraces.write_success_18.instrs.instr_map ++
  IslaTraces.write_success_19.instrs.instr_map ++
  IslaTraces.write_success_20.instrs.instr_map ++
  IslaTraces.write_success_21.instrs.instr_map ++
  IslaTraces.write_success_22.instrs.instr_map ++
  IslaTraces.write_success_23.instrs.instr_map ++
  IslaTraces.write_success_24.instrs.instr_map ++
  IslaTraces.write_success_25.instrs.instr_map ++
  IslaTraces.write_success_26.instrs.instr_map ++
  IslaTraces.write_success_27.instrs.instr_map ++
  IslaTraces.write_success_28.instrs.instr_map ++
  IslaTraces.write_success_29.instrs.instr_map ++
  IslaTraces.write_success_30.instrs.instr_map ++
  IslaTraces.write_success_31.instrs.instr_map ++
  IslaTraces.write_success_32.instrs.instr_map ++
  IslaTraces.write_success_33.instrs.instr_map ++
  IslaTraces.write_success_34.instrs.instr_map ++
  IslaTraces.write_success_35.instrs.instr_map ++
  IslaTraces.write_success_36.instrs.instr_map ++
  IslaTraces.write_success_37.instrs.instr_map ++
  IslaTraces.write_success_38.instrs.instr_map ++
  IslaTraces.write_success_39.instrs.instr_map ++
  IslaTraces.write_success_40.instrs.instr_map ++
  IslaTraces.write_success_41.instrs.instr_map ++
  IslaTraces.write_success_42.instrs.instr_map ++
  IslaTraces.write_success_43.instrs.instr_map ++
  IslaTraces.write_success_44.instrs.instr_map ++
  IslaTraces.write_success_45.instrs.instr_map ++
  IslaTraces.write_success_46.instrs.instr_map ++
  IslaTraces.write_success_47.instrs.instr_map ++
  IslaTraces.write_success_48.instrs.instr_map ++
  IslaTraces.write_success_49.instrs.instr_map ++
  IslaTraces.write_success_50.instrs.instr_map ++
  IslaTraces.write_success_51.instrs.instr_map ++
  IslaTraces.write_success_52.instrs.instr_map ++
  IslaTraces.write_success_53.instrs.instr_map ++
  IslaTraces.write_success_54.instrs.instr_map ++
  IslaTraces.write_success_55.instrs.instr_map ++
  IslaTraces.write_success_56.instrs.instr_map ++
  IslaTraces.write_success_57.instrs.instr_map ++
  IslaTraces.write_success_58.instrs.instr_map ++
  IslaTraces.write_success_59.instrs.instr_map ++
  IslaTraces.write_success_60.instrs.instr_map ++
  IslaTraces.write_success_61.instrs.instr_map ++
  IslaTraces.write_success_62.instrs.instr_map ++
  IslaTraces.write_success_63.instrs.instr_map ++
  IslaTraces.write_success_64.instrs.instr_map ++
  IslaTraces.write_success_65.instrs.instr_map ++
  IslaTraces.write_success_66.instrs.instr_map ++
  IslaTraces.write_success_67.instrs.instr_map ++
  IslaTraces.write_success_68.instrs.instr_map ++
  IslaTraces.write_success_69.instrs.instr_map ++
  IslaTraces.write_success_70.instrs.instr_map ++
  IslaTraces.write_success_71.instrs.instr_map ++
  IslaTraces.write_success_72.instrs.instr_map ++
  IslaTraces.write_success_73.instrs.instr_map ++
  IslaTraces.write_success_74.instrs.instr_map ++
  IslaTraces.write_success_75.instrs.instr_map ++
  IslaTraces.write_success_76.instrs.instr_map ++
  IslaTraces.write_success_77.instrs.instr_map ++
  IslaTraces.write_success_78.instrs.instr_map ++
  IslaTraces.write_success_79.instrs.instr_map ++
  IslaTraces.write_success_80.instrs.instr_map ++
  IslaTraces.write_success_81.instrs.instr_map ++
  IslaTraces.write_success_82.instrs.instr_map ++
  IslaTraces.write_success_83.instrs.instr_map ++
  IslaTraces.write_success_84.instrs.instr_map ++
  IslaTraces.write_success_85.instrs.instr_map ++
  IslaTraces.write_success_86.instrs.instr_map ++
  IslaTraces.write_success_87.instrs.instr_map ++
  IslaTraces.write_success_88.instrs.instr_map ++
  IslaTraces.write_success_89.instrs.instr_map ++
  IslaTraces.write_success_90.instrs.instr_map ++
  IslaTraces.write_success_91.instrs.instr_map ++
  IslaTraces.write_success_92.instrs.instr_map ++
  IslaTraces.write_success_93.instrs.instr_map ++
  IslaTraces.write_success_94.instrs.instr_map ++
  IslaTraces.write_success_95.instrs.instr_map ++
  IslaTraces.write_success_96.instrs.instr_map ++
  IslaTraces.write_success_97.instrs.instr_map ++
  IslaTraces.write_success_98.instrs.instr_map ++
  IslaTraces.write_success_99.instrs.instr_map ++
  IslaTraces.write_success_100.instrs.instr_map ++
  IslaTraces.write_success_101.instrs.instr_map ++
  IslaTraces.write_success_102.instrs.instr_map ++
  IslaTraces.write_success_103.instrs.instr_map ++
  IslaTraces.write_success_104.instrs.instr_map ++
  IslaTraces.write_success_105.instrs.instr_map ++
  IslaTraces.write_success_106.instrs.instr_map ++
  IslaTraces.write_success_107.instrs.instr_map ++
  IslaTraces.write_success_108.instrs.instr_map ++
  IslaTraces.write_success_109.instrs.instr_map ++
  IslaTraces.write_success_110.instrs.instr_map ++
  IslaTraces.write_success_111.instrs.instr_map ++
  IslaTraces.write_success_112.instrs.instr_map ++
  IslaTraces.write_success_113.instrs.instr_map ++
  IslaTraces.write_success_114.instrs.instr_map ++
  IslaTraces.write_success_115.instrs.instr_map ++
  IslaTraces.write_success_116.instrs.instr_map ++
  IslaTraces.write_success_117.instrs.instr_map ++
  IslaTraces.write_success_118.instrs.instr_map ++
  IslaTraces.write_success_119.instrs.instr_map ++
  IslaTraces.write_success_120.instrs.instr_map ++
  IslaTraces.write_success_121.instrs.instr_map ++
  IslaTraces.write_success_122.instrs.instr_map ++
  IslaTraces.write_success_123.instrs.instr_map ++
  IslaTraces.write_success_124.instrs.instr_map ++
  IslaTraces.write_success_125.instrs.instr_map ++
  IslaTraces.write_success_126.instrs.instr_map ++
  IslaTraces.write_success_127.instrs.instr_map.

Definition zesuTerminationProgramEntries : list (addr * isla_trace) :=
  (fun entry => (Z_to_bv 64 entry.1, entry.2)) <$> zesuTerminationProgramEntriesZ.

Definition zesuTerminationProgram : gmap addr isla_trace :=
  list_to_map zesuTerminationProgramEntries.

Lemma zesu_termination_program_size :
  size zesuTerminationProgram = 998%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma zesu_termination_program_terminal_absent :
  zesuTerminationProgram !! BV 64 0x101d0 = None.
Proof. vm_compute. reflexivity. Qed.

Lemma zesu_termination_program_canonical_output_data :
  zesuTerminationProgram !! BV 64 0x10198 =
    Some IslaTraces.write_success_01.a10198.a10198.
Proof. vm_compute. reflexivity. Qed.

Lemma zesu_termination_program_canonical_output_size :
  zesuTerminationProgram !! BV 64 0x1019c =
    Some IslaTraces.write_success_01.a1019c.a1019c.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions zesu_termination_program_terminal_absent.
Print Assumptions zesu_termination_program_size.
Print Assumptions zesu_termination_program_canonical_output_data.
Print Assumptions zesu_termination_program_canonical_output_size.
