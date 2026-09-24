Require Import ZesuSsz.Automation.All.
Require Import isla.opsem.
From stdpp Require Import gmap.
From Coq Require Import Lists.List.
Require Import IslaTraces.write_success_blocks.Index.
Require Import IslaTraces.decoder_00.instrs.
Require Import IslaTraces.decoder_01.instrs.
Require Import IslaTraces.decoder_02.instrs.
Require Import IslaTraces.decoder_03.instrs.
Require Import IslaTraces.decoder_04.instrs.
Require Import IslaTraces.decoder_05.instrs.
Require Import IslaTraces.decoder_06.instrs.
Require Import IslaTraces.decoder_07.instrs.
Require Import IslaTraces.decoder_08.instrs.
Require Import IslaTraces.decoder_09.instrs.
Require Import IslaTraces.decoder_10.instrs.
Require Import IslaTraces.decoder_11.instrs.
Require Import IslaTraces.decoder_12.instrs.
Require Import IslaTraces.decoder_13.instrs.
Require Import IslaTraces.decoder_14.instrs.
Require Import IslaTraces.decoder_15.instrs.
Require Import IslaTraces.decoder_16.instrs.
Require Import IslaTraces.decoder_17.instrs.
Require Import IslaTraces.decoder_18.instrs.
Require Import IslaTraces.decoder_19.instrs.
Require Import IslaTraces.decoder_20.instrs.
Require Import IslaTraces.decoder_21.instrs.
Require Import IslaTraces.decoder_22.instrs.
Require Import IslaTraces.decoder_23.instrs.
Require Import IslaTraces.decoder_24.instrs.
Require Import IslaTraces.decoder_25.instrs.
Require Import IslaTraces.decoder_26.instrs.
Require Import IslaTraces.decoder_27.instrs.
Require Import IslaTraces.decoder_28.instrs.
Require Import IslaTraces.decoder_29.instrs.
Require Import IslaTraces.decoder_30.instrs.
Require Import IslaTraces.decoder_31.instrs.
Require Import IslaTraces.decoder_32.instrs.
Require Import IslaTraces.decoder_33.instrs.
Require Import IslaTraces.decoder_34.instrs.
Require Import IslaTraces.decoder_35.instrs.
Require Import IslaTraces.decoder_36.instrs.
Require Import IslaTraces.decoder_37.instrs.
Require Import IslaTraces.decoder_38.instrs.
Require Import IslaTraces.decoder_39.instrs.
Require Import IslaTraces.decoder_40.instrs.
Require Import IslaTraces.decoder_41.instrs.
Require Import IslaTraces.decoder_42.instrs.
Require Import IslaTraces.decoder_43.instrs.
Require Import IslaTraces.decoder_44.instrs.
Require Import IslaTraces.decoder_45.instrs.
Require Import IslaTraces.decoder_46.instrs.
Require Import IslaTraces.decoder_47.instrs.
Require Import IslaTraces.decoder_48.instrs.
Require Import IslaTraces.decoder_49.instrs.
Require Import IslaTraces.decoder_50.instrs.
Require Import IslaTraces.decoder_51.instrs.
Require Import IslaTraces.decoder_52.instrs.
Require Import IslaTraces.decoder_53.instrs.
Require Import IslaTraces.decoder_54.instrs.
Require Import IslaTraces.decoder_55.instrs.
Require Import IslaTraces.decoder_56.instrs.
Require Import IslaTraces.decoder_57.instrs.
Require Import IslaTraces.decoder_58.instrs.
Require Import IslaTraces.decoder_59.instrs.
Require Import IslaTraces.decoder_60.instrs.
Require Import IslaTraces.decoder_61.instrs.
Require Import IslaTraces.decoder_62.instrs.
Require Import IslaTraces.decoder_63.instrs.
Require Import IslaTraces.decoder_64.instrs.
Require Import IslaTraces.decoder_65.instrs.
Require Import IslaTraces.decoder_66.instrs.
Require Import IslaTraces.decoder_67.instrs.
Require Import IslaTraces.decoder_68.instrs.
Require Import IslaTraces.decoder_69.instrs.
Require Import IslaTraces.decoder_70.instrs.
Require Import IslaTraces.decoder_71.instrs.
Require Import IslaTraces.decoder_72.instrs.
Require Import IslaTraces.decoder_73.instrs.
Require Import IslaTraces.decoder_74.instrs.
Require Import IslaTraces.decoder_75.instrs.
Require Import IslaTraces.decoder_76.instrs.
Require Import IslaTraces.decoder_77.instrs.
Require Import IslaTraces.decoder_78.instrs.
Require Import IslaTraces.decoder_79.instrs.
Require Import IslaTraces.decoder_80.instrs.
Require Import IslaTraces.decoder_81.instrs.
Require Import IslaTraces.decoder_82.instrs.
Require Import IslaTraces.decoder_83.instrs.
Require Import IslaTraces.decoder_84.instrs.
Require Import IslaTraces.decoder_85.instrs.
Require Import IslaTraces.decoder_86.instrs.
Require Import IslaTraces.decoder_87.instrs.
Require Import IslaTraces.decoder_88.instrs.
Require Import IslaTraces.decoder_89.instrs.
Require Import IslaTraces.decoder_90.instrs.
Require Import IslaTraces.decoder_91.instrs.
Require Import IslaTraces.decoder_92.instrs.
Require Import IslaTraces.decoder_93.instrs.
Require Import IslaTraces.decoder_94.instrs.
Require Import IslaTraces.decoder_95.instrs.
Require Import IslaTraces.decoder_96.instrs.
Require Import IslaTraces.decoder_97.instrs.
Require Import IslaTraces.decoder_98.instrs.
Require Import IslaTraces.decoder_99.instrs.
Require Import IslaTraces.decoder_100.instrs.
Require Import IslaTraces.decoder_101.instrs.
Require Import IslaTraces.decoder_102.instrs.
Require Import IslaTraces.decoder_103.instrs.
Require Import IslaTraces.decoder_104.instrs.
Require Import IslaTraces.decoder_105.instrs.
Require Import IslaTraces.decoder_106.instrs.
Require Import IslaTraces.decoder_107.instrs.
Require Import IslaTraces.decoder_108.instrs.
Require Import IslaTraces.decoder_109.instrs.
Require Import IslaTraces.decoder_110.instrs.
Require Import IslaTraces.decoder_111.instrs.
Require Import IslaTraces.decoder_112.instrs.
Require Import IslaTraces.decoder_113.instrs.
Require Import IslaTraces.decoder_114.instrs.
Require Import IslaTraces.decoder_115.instrs.
Require Import IslaTraces.decoder_116.instrs.
Require Import IslaTraces.decoder_117.instrs.
Require Import IslaTraces.decoder_118.instrs.
Require Import IslaTraces.decoder_119.instrs.
Require Import IslaTraces.decoder_120.instrs.
Require Import IslaTraces.decoder_121.instrs.
Require Import IslaTraces.decoder_122.instrs.
Require Import IslaTraces.decoder_123.instrs.
Require Import IslaTraces.decoder_124.instrs.
Require Import IslaTraces.decoder_125.instrs.
Require Import IslaTraces.decoder_126.instrs.
Require Import IslaTraces.decoder_127.instrs.
Require Import IslaTraces.decoder_128.instrs.
Require Import IslaTraces.decoder_129.instrs.
Require Import IslaTraces.decoder_130.instrs.
Require Import IslaTraces.decoder_131.instrs.
Require Import IslaTraces.decoder_132.instrs.
Require Import IslaTraces.decoder_133.instrs.
Require Import IslaTraces.decoder_134.instrs.
Require Import IslaTraces.decoder_135.instrs.
Require Import IslaTraces.decoder_136.instrs.
Require Import IslaTraces.decoder_137.instrs.
Require Import IslaTraces.decoder_138.instrs.
Require Import IslaTraces.decoder_139.instrs.
Require Import IslaTraces.decoder_140.instrs.
Require Import IslaTraces.decoder_141.instrs.
Require Import IslaTraces.decoder_142.instrs.
Require Import IslaTraces.decoder_143.instrs.
Require Import IslaTraces.decoder_144.instrs.
Require Import IslaTraces.decoder_145.instrs.
Require Import IslaTraces.decoder_146.instrs.
Require Import IslaTraces.decoder_147.instrs.
Require Import IslaTraces.decoder_148.instrs.
Require Import IslaTraces.decoder_149.instrs.
Require Import IslaTraces.decoder_150.instrs.
Require Import IslaTraces.decoder_151.instrs.
Require Import IslaTraces.decoder_152.instrs.
Require Import IslaTraces.decoder_153.instrs.
Require Import IslaTraces.decoder_154.instrs.
Require Import IslaTraces.decoder_155.instrs.
Require Import IslaTraces.decoder_156.instrs.
Require Import IslaTraces.decoder_157.instrs.
Require Import IslaTraces.decoder_158.instrs.
Require Import IslaTraces.decoder_159.instrs.
Require Import IslaTraces.decoder_160.instrs.
Require Import IslaTraces.decoder_161.instrs.
Require Import IslaTraces.decoder_162.instrs.
Require Import IslaTraces.decoder_163.instrs.
Require Import IslaTraces.decoder_164.instrs.
Require Import IslaTraces.decoder_165.instrs.
Require Import IslaTraces.decoder_166.instrs.
Require Import IslaTraces.decoder_167.instrs.
Require Import IslaTraces.decoder_168.instrs.
Require Import IslaTraces.decoder_169.instrs.
Require Import IslaTraces.decoder_170.instrs.
Require Import IslaTraces.decoder_171.instrs.
Require Import IslaTraces.decoder_172.instrs.
Require Import IslaTraces.decoder_173.instrs.
Require Import IslaTraces.decoder_174.instrs.
Require Import IslaTraces.decoder_175.instrs.
Require Import IslaTraces.decoder_176.instrs.
Require Import IslaTraces.decoder_177.instrs.
Require Import IslaTraces.decoder_178.instrs.
Require Import IslaTraces.decoder_179.instrs.
Require Import IslaTraces.decoder_180.instrs.
Require Import IslaTraces.decoder_181.instrs.
Require Import IslaTraces.decoder_182.instrs.
Require Import IslaTraces.decoder_183.instrs.
Require Import IslaTraces.decoder_184.instrs.
Require Import IslaTraces.decoder_185.instrs.
Require Import IslaTraces.decoder_186.instrs.
Require Import IslaTraces.decoder_187.instrs.
Require Import IslaTraces.decoder_188.instrs.
Require Import IslaTraces.decoder_189.instrs.
Require Import IslaTraces.decoder_190.instrs.
Require Import IslaTraces.decoder_191.instrs.
Require Import IslaTraces.decoder_192.instrs.
Require Import IslaTraces.decoder_193.instrs.
Require Import IslaTraces.decoder_194.instrs.
Require Import IslaTraces.decoder_195.instrs.
Require Import IslaTraces.decoder_196.instrs.
Require Import IslaTraces.decoder_197.instrs.
Require Import IslaTraces.decoder_198.instrs.
Require Import IslaTraces.decoder_199.instrs.
Require Import IslaTraces.decoder_200.instrs.
Require Import IslaTraces.decoder_201.instrs.
Require Import IslaTraces.decoder_202.instrs.
Require Import IslaTraces.decoder_203.instrs.
Require Import IslaTraces.decoder_204.instrs.
Require Import IslaTraces.decoder_205.instrs.
Require Import IslaTraces.decoder_206.instrs.
Require Import IslaTraces.decoder_207.instrs.
Require Import IslaTraces.decoder_208.instrs.
Require Import IslaTraces.decoder_209.instrs.
Require Import IslaTraces.decoder_210.instrs.
Require Import IslaTraces.decoder_211.instrs.
Require Import IslaTraces.decoder_212.instrs.
Require Import IslaTraces.decoder_213.instrs.
Require Import IslaTraces.decoder_214.instrs.
Require Import IslaTraces.decoder_215.instrs.
Require Import IslaTraces.decoder_216.instrs.
Require Import IslaTraces.decoder_217.instrs.
Require Import IslaTraces.decoder_218.instrs.
Require Import IslaTraces.decoder_219.instrs.
Require Import IslaTraces.decoder_220.instrs.
Require Import IslaTraces.decoder_221.instrs.
Require Import IslaTraces.decoder_222.instrs.
Require Import IslaTraces.decoder_223.instrs.
Require Import IslaTraces.decoder_224.instrs.
Require Import IslaTraces.decoder_225.instrs.
Require Import IslaTraces.decoder_226.instrs.
Require Import IslaTraces.decoder_227.instrs.
Require Import IslaTraces.decoder_228.instrs.
Require Import IslaTraces.decoder_229.instrs.
Require Import IslaTraces.decoder_230.instrs.
Require Import IslaTraces.decoder_231.instrs.
Require Import IslaTraces.decoder_232.instrs.
Require Import IslaTraces.decoder_233.instrs.
Require Import IslaTraces.decoder_234.instrs.
Require Import IslaTraces.decoder_235.instrs.
Require Import IslaTraces.decoder_236.instrs.
Require Import IslaTraces.decoder_237.instrs.
Require Import IslaTraces.decoder_238.instrs.
Require Import IslaTraces.decoder_239.instrs.
Require Import IslaTraces.decoder_240.instrs.
Require Import IslaTraces.decoder_241.instrs.
Require Import IslaTraces.decoder_242.instrs.
Require Import IslaTraces.decoder_243.instrs.
Require Import IslaTraces.decoder_244.instrs.
Require Import IslaTraces.decoder_245.instrs.
Require Import IslaTraces.decoder_246.instrs.
Require Import IslaTraces.decoder_247.instrs.
Require Import IslaTraces.decoder_248.instrs.
Require Import IslaTraces.decoder_249.instrs.
Require Import IslaTraces.decoder_250.instrs.
Require Import IslaTraces.decoder_251.instrs.
Require Import IslaTraces.decoder_252.instrs.
Require Import IslaTraces.decoder_253.instrs.
Require Import IslaTraces.decoder_254.instrs.
Require Import IslaTraces.decoder_255.instrs.
Require Import IslaTraces.decoder_256.instrs.
Require Import IslaTraces.decoder_257.instrs.
Require Import IslaTraces.decoder_258.instrs.
Require Import IslaTraces.decoder_259.instrs.
Require Import IslaTraces.decoder_260.instrs.
Require Import IslaTraces.decoder_261.instrs.
Require Import IslaTraces.decoder_262.instrs.
Require Import IslaTraces.decoder_263.instrs.
Require Import IslaTraces.decoder_264.instrs.
Require Import IslaTraces.decoder_265.instrs.
Require Import IslaTraces.decoder_266.instrs.
Require Import IslaTraces.decoder_267.instrs.
Require Import IslaTraces.decoder_268.instrs.
Require Import IslaTraces.decoder_269.instrs.
Require Import IslaTraces.decoder_270.instrs.
Require Import IslaTraces.decoder_271.instrs.
Require Import IslaTraces.decoder_272.instrs.
Require Import IslaTraces.decoder_273.instrs.
Require Import IslaTraces.decoder_274.instrs.
Require Import IslaTraces.decoder_275.instrs.
Require Import IslaTraces.decoder_276.instrs.
Require Import IslaTraces.decoder_277.instrs.
Require Import IslaTraces.startup.instrs.
Require Import IslaTraces.main.instrs.
Require Import IslaTraces.read_input.instrs.
Require Import IslaTraces.allocator_get.instrs.
Require Import IslaTraces.write_failure.instrs.
Require Import IslaTraces.zkvm_exit.instrs.
Require Import IslaTraces.write_success_00.instrs.
Require Import IslaTraces.write_success_01.instrs.
Require Import IslaTraces.write_success_02.instrs.
Require Import IslaTraces.write_success_03.instrs.
Require Import IslaTraces.write_success_04.instrs.
Require Import IslaTraces.write_success_05.instrs.
Require Import IslaTraces.write_success_06.instrs.
Require Import IslaTraces.write_success_07.instrs.
Require Import IslaTraces.write_success_08.instrs.
Require Import IslaTraces.write_success_127.instrs.

Definition pinnedIndexAddresses : list Z := [
  0x14d30%Z; 0x14d34%Z; 0x14d38%Z; 0x14d3c%Z; 0x14d40%Z; 0x14d44%Z; 0x14d48%Z; 0x14d4c%Z; 0x14d50%Z; 0x14d54%Z; 0x14d58%Z; 0x14d5c%Z;
  0x14d60%Z; 0x14d64%Z; 0x14d68%Z; 0x14d6c%Z; 0x14d70%Z; 0x14d74%Z; 0x14d78%Z; 0x14d7c%Z; 0x14d80%Z; 0x14d84%Z; 0x14d88%Z; 0x14d8c%Z;
  0x14d90%Z; 0x14d94%Z; 0x14d98%Z; 0x14d9c%Z; 0x14da0%Z; 0x14da4%Z; 0x14da8%Z; 0x14dac%Z; 0x14db0%Z; 0x14db4%Z; 0x14db8%Z; 0x14dbc%Z;
  0x14dc0%Z; 0x14dc4%Z; 0x14dc8%Z; 0x14dcc%Z; 0x14dd0%Z; 0x14dd4%Z; 0x14dd8%Z; 0x14ddc%Z; 0x14de0%Z; 0x14de4%Z; 0x14de8%Z; 0x14dec%Z;
  0x14df0%Z; 0x14df4%Z; 0x14df8%Z; 0x14dfc%Z; 0x14e00%Z; 0x14e04%Z; 0x14e08%Z; 0x14e0c%Z; 0x14e10%Z; 0x14e14%Z; 0x14e18%Z; 0x14e1c%Z;
  0x14e20%Z; 0x14e24%Z; 0x14e28%Z; 0x14e2c%Z; 0x14e30%Z; 0x14e34%Z; 0x14e38%Z; 0x14e3c%Z; 0x14e40%Z; 0x14e44%Z; 0x14e48%Z; 0x14e4c%Z;
  0x14e50%Z; 0x14e54%Z; 0x14e58%Z; 0x14e5c%Z; 0x14e60%Z; 0x14e64%Z; 0x14e68%Z; 0x14e6c%Z; 0x14e70%Z; 0x14e74%Z; 0x14e78%Z; 0x14e7c%Z;
  0x14e80%Z; 0x14e84%Z; 0x14e88%Z; 0x14e8c%Z; 0x14e90%Z; 0x14e94%Z; 0x14e98%Z; 0x14e9c%Z; 0x14ea0%Z; 0x14ea4%Z; 0x14ea8%Z; 0x14eac%Z;
  0x14eb0%Z; 0x14eb4%Z; 0x14eb8%Z; 0x14ebc%Z; 0x14ec0%Z; 0x14ec4%Z; 0x14ec8%Z; 0x14ecc%Z; 0x14ed0%Z; 0x14ed4%Z; 0x14ed8%Z; 0x14edc%Z;
  0x14ee0%Z; 0x14ee4%Z; 0x14ee8%Z; 0x14eec%Z; 0x14ef0%Z; 0x14ef4%Z; 0x14ef8%Z; 0x14efc%Z; 0x14f00%Z; 0x14f04%Z; 0x14f08%Z; 0x14f0c%Z;
  0x14f10%Z; 0x14f14%Z; 0x14f18%Z; 0x14f1c%Z; 0x14f20%Z; 0x14f24%Z; 0x14f28%Z; 0x14f2c%Z; 0x14f30%Z; 0x14f34%Z; 0x14f38%Z; 0x14f3c%Z;
  0x14f40%Z; 0x14f44%Z; 0x14f48%Z; 0x14f4c%Z; 0x14f50%Z; 0x14f54%Z; 0x14f58%Z; 0x14f5c%Z; 0x14f60%Z; 0x14f64%Z; 0x14f68%Z; 0x14f6c%Z;
  0x14f70%Z; 0x14f74%Z; 0x14f78%Z; 0x14f7c%Z; 0x14f80%Z; 0x14f84%Z; 0x14f88%Z; 0x14f8c%Z; 0x14f90%Z; 0x14f94%Z; 0x14f98%Z; 0x14f9c%Z;
  0x14fa0%Z; 0x14fa4%Z; 0x14fa8%Z; 0x14fac%Z; 0x14fb0%Z; 0x14fb4%Z; 0x14fb8%Z; 0x14fbc%Z; 0x14fc0%Z; 0x14fc4%Z; 0x14fc8%Z; 0x14fcc%Z;
  0x14fd0%Z; 0x14fd4%Z; 0x14fd8%Z; 0x14fdc%Z; 0x14fe0%Z; 0x14fe4%Z; 0x14fe8%Z; 0x14fec%Z; 0x14ff0%Z; 0x14ff4%Z; 0x14ff8%Z; 0x14ffc%Z;
  0x15000%Z; 0x15004%Z; 0x15008%Z; 0x1500c%Z; 0x15010%Z; 0x15014%Z; 0x15018%Z; 0x1501c%Z; 0x15020%Z; 0x15024%Z; 0x15028%Z; 0x1502c%Z;
  0x15030%Z; 0x15034%Z; 0x15038%Z; 0x1503c%Z; 0x15040%Z; 0x15044%Z; 0x15048%Z; 0x1504c%Z; 0x15050%Z; 0x15054%Z; 0x15058%Z; 0x1505c%Z;
  0x15060%Z; 0x15064%Z; 0x15068%Z; 0x1506c%Z; 0x15070%Z; 0x15074%Z; 0x15078%Z; 0x1507c%Z; 0x15080%Z; 0x15084%Z; 0x15088%Z; 0x1508c%Z;
  0x15090%Z; 0x15094%Z; 0x15098%Z; 0x1509c%Z; 0x150a0%Z; 0x150a4%Z; 0x150a8%Z; 0x150ac%Z; 0x150b0%Z; 0x150b4%Z; 0x150b8%Z; 0x150bc%Z;
  0x150c0%Z; 0x150c4%Z; 0x150c8%Z; 0x150cc%Z; 0x150d0%Z; 0x150d4%Z; 0x150d8%Z; 0x150dc%Z; 0x150e0%Z; 0x150e4%Z; 0x150e8%Z; 0x150ec%Z;
  0x150f0%Z; 0x150f4%Z; 0x150f8%Z; 0x150fc%Z; 0x15100%Z; 0x15104%Z; 0x15108%Z; 0x1510c%Z; 0x15110%Z; 0x15114%Z; 0x15118%Z; 0x1511c%Z;
  0x15120%Z; 0x15124%Z; 0x15128%Z; 0x1512c%Z; 0x15130%Z; 0x15134%Z; 0x15138%Z; 0x1513c%Z; 0x15140%Z; 0x15144%Z; 0x15148%Z; 0x1514c%Z;
  0x15150%Z; 0x15154%Z; 0x15158%Z; 0x1515c%Z; 0x15160%Z; 0x15164%Z; 0x15168%Z; 0x1516c%Z; 0x15170%Z; 0x15174%Z; 0x15178%Z; 0x1517c%Z;
  0x15180%Z; 0x15184%Z; 0x15188%Z; 0x1518c%Z; 0x15190%Z; 0x15194%Z; 0x15198%Z; 0x1519c%Z; 0x151a0%Z; 0x151a4%Z; 0x151a8%Z; 0x151ac%Z;
  0x151b0%Z; 0x151b4%Z; 0x151b8%Z; 0x151bc%Z; 0x151c0%Z; 0x151c4%Z; 0x151c8%Z; 0x151cc%Z; 0x151d0%Z; 0x151d4%Z; 0x151d8%Z; 0x151dc%Z;
  0x151e0%Z; 0x151e4%Z; 0x151e8%Z; 0x151ec%Z; 0x151f0%Z; 0x151f4%Z; 0x151f8%Z; 0x151fc%Z; 0x15200%Z; 0x15204%Z; 0x15208%Z; 0x1520c%Z;
  0x15210%Z; 0x15214%Z; 0x15218%Z; 0x1521c%Z; 0x15220%Z; 0x15224%Z; 0x15228%Z; 0x1522c%Z; 0x15230%Z; 0x15234%Z; 0x15238%Z; 0x1523c%Z;
  0x15240%Z; 0x15244%Z; 0x15248%Z; 0x1524c%Z; 0x15250%Z; 0x15254%Z; 0x15258%Z; 0x1525c%Z; 0x15260%Z; 0x15264%Z; 0x15268%Z; 0x1526c%Z;
  0x15270%Z; 0x15274%Z; 0x15278%Z; 0x1527c%Z; 0x15280%Z; 0x15284%Z; 0x15288%Z; 0x1528c%Z; 0x15290%Z; 0x15294%Z; 0x15298%Z; 0x1529c%Z;
  0x152a0%Z; 0x152a4%Z; 0x152a8%Z; 0x152ac%Z; 0x152b0%Z; 0x152b4%Z; 0x152b8%Z; 0x152bc%Z; 0x152c0%Z; 0x152c4%Z; 0x152c8%Z; 0x152cc%Z;
  0x152d0%Z; 0x152d4%Z; 0x152d8%Z; 0x152dc%Z; 0x152e0%Z; 0x152e4%Z; 0x152e8%Z; 0x152ec%Z; 0x152f0%Z; 0x152f4%Z; 0x152f8%Z; 0x152fc%Z;
  0x15300%Z; 0x15304%Z; 0x15308%Z; 0x1530c%Z; 0x15310%Z; 0x15314%Z; 0x15318%Z; 0x1531c%Z; 0x15320%Z; 0x15324%Z; 0x15328%Z; 0x1532c%Z;
  0x15330%Z; 0x15334%Z; 0x15338%Z; 0x1533c%Z; 0x15340%Z; 0x15344%Z; 0x15348%Z; 0x1534c%Z; 0x15350%Z; 0x15354%Z; 0x15358%Z; 0x1535c%Z;
  0x15360%Z; 0x15364%Z; 0x15368%Z; 0x1536c%Z; 0x15370%Z; 0x15374%Z; 0x15378%Z; 0x1537c%Z; 0x15380%Z; 0x15384%Z; 0x15388%Z; 0x1538c%Z;
  0x15390%Z; 0x15394%Z; 0x15398%Z; 0x1539c%Z; 0x153a0%Z; 0x153a4%Z; 0x153a8%Z; 0x153ac%Z; 0x153b0%Z; 0x153b4%Z; 0x153b8%Z; 0x153bc%Z;
  0x153c0%Z; 0x153c4%Z; 0x153c8%Z; 0x153cc%Z; 0x153d0%Z; 0x153d4%Z; 0x153d8%Z; 0x153dc%Z; 0x153e0%Z; 0x153e4%Z; 0x153e8%Z; 0x153ec%Z;
  0x153f0%Z; 0x153f4%Z; 0x153f8%Z; 0x153fc%Z; 0x15400%Z; 0x15404%Z; 0x15408%Z; 0x1540c%Z; 0x15410%Z; 0x15414%Z; 0x15418%Z; 0x1541c%Z;
  0x15420%Z; 0x15424%Z; 0x15428%Z; 0x1542c%Z; 0x15430%Z; 0x15434%Z; 0x15438%Z; 0x1543c%Z; 0x15440%Z; 0x15444%Z; 0x15448%Z; 0x1544c%Z;
  0x15450%Z; 0x15454%Z; 0x15458%Z; 0x1545c%Z; 0x15460%Z; 0x15464%Z; 0x15468%Z; 0x1546c%Z; 0x15470%Z; 0x15474%Z; 0x15478%Z; 0x1547c%Z;
  0x15480%Z; 0x15484%Z; 0x15488%Z; 0x1548c%Z; 0x15490%Z; 0x15494%Z; 0x15498%Z; 0x1549c%Z; 0x154a0%Z; 0x154a4%Z; 0x154a8%Z; 0x154ac%Z;
  0x154b0%Z; 0x154b4%Z; 0x154b8%Z; 0x154bc%Z; 0x154c0%Z; 0x154c4%Z; 0x154c8%Z; 0x154cc%Z; 0x154d0%Z; 0x154d4%Z; 0x154d8%Z; 0x154dc%Z;
  0x154e0%Z; 0x154e4%Z; 0x154e8%Z; 0x154ec%Z; 0x154f0%Z; 0x154f4%Z; 0x154f8%Z; 0x154fc%Z; 0x15500%Z; 0x15504%Z; 0x15508%Z; 0x1550c%Z;
  0x15510%Z; 0x15514%Z; 0x15518%Z; 0x1551c%Z; 0x15520%Z; 0x15524%Z; 0x15528%Z; 0x1552c%Z; 0x15530%Z; 0x15534%Z; 0x15538%Z; 0x1553c%Z;
  0x15540%Z; 0x15544%Z; 0x15548%Z; 0x1554c%Z; 0x15550%Z; 0x15554%Z; 0x15558%Z; 0x1555c%Z; 0x15560%Z; 0x15564%Z; 0x15568%Z; 0x1556c%Z;
  0x15570%Z; 0x15574%Z; 0x15578%Z; 0x1557c%Z; 0x15580%Z; 0x15584%Z; 0x15588%Z; 0x1558c%Z; 0x15590%Z; 0x15594%Z; 0x15598%Z; 0x1559c%Z;
  0x155a0%Z; 0x155a4%Z; 0x155a8%Z; 0x155ac%Z; 0x155b0%Z; 0x155b4%Z; 0x155b8%Z; 0x155bc%Z; 0x155c0%Z; 0x155c4%Z; 0x155c8%Z; 0x155cc%Z;
  0x155d0%Z; 0x155d4%Z; 0x155d8%Z; 0x155dc%Z; 0x155e0%Z; 0x155e4%Z; 0x155e8%Z; 0x155ec%Z; 0x155f0%Z; 0x155f4%Z; 0x155f8%Z; 0x155fc%Z;
  0x15600%Z; 0x15604%Z; 0x15608%Z; 0x1560c%Z; 0x15610%Z; 0x15614%Z; 0x15618%Z; 0x1561c%Z; 0x15620%Z; 0x15624%Z; 0x15628%Z; 0x1562c%Z;
  0x15630%Z; 0x15634%Z; 0x15638%Z; 0x1563c%Z; 0x15640%Z; 0x15644%Z; 0x15648%Z; 0x1564c%Z; 0x15650%Z; 0x15654%Z; 0x15658%Z; 0x1565c%Z;
  0x15660%Z; 0x15664%Z; 0x15668%Z; 0x1566c%Z; 0x15670%Z; 0x15674%Z; 0x15678%Z; 0x1567c%Z; 0x15680%Z; 0x15684%Z; 0x15688%Z; 0x1568c%Z;
  0x15690%Z; 0x15694%Z; 0x15698%Z; 0x1569c%Z; 0x156a0%Z; 0x156a4%Z; 0x156a8%Z; 0x156ac%Z; 0x156b0%Z; 0x156b4%Z; 0x156b8%Z; 0x156bc%Z;
  0x156c0%Z; 0x156c4%Z; 0x156c8%Z; 0x156cc%Z; 0x156d0%Z; 0x156d4%Z; 0x156d8%Z; 0x156dc%Z; 0x156e0%Z; 0x156e4%Z; 0x156e8%Z; 0x156ec%Z;
  0x156f0%Z; 0x156f4%Z; 0x156f8%Z; 0x156fc%Z; 0x15700%Z; 0x15704%Z; 0x15708%Z; 0x1570c%Z; 0x15710%Z; 0x15714%Z; 0x15718%Z; 0x1571c%Z;
  0x15720%Z; 0x15724%Z; 0x15728%Z; 0x1572c%Z; 0x15730%Z; 0x15734%Z; 0x15738%Z; 0x1573c%Z; 0x15740%Z; 0x15744%Z; 0x15748%Z; 0x1574c%Z;
  0x15750%Z; 0x15754%Z; 0x15758%Z; 0x1575c%Z; 0x15760%Z; 0x15764%Z; 0x15768%Z; 0x1576c%Z; 0x15770%Z; 0x15774%Z; 0x15778%Z; 0x1577c%Z;
  0x15780%Z; 0x15784%Z; 0x15788%Z; 0x1578c%Z; 0x15790%Z; 0x15794%Z; 0x15798%Z; 0x1579c%Z; 0x157a0%Z; 0x157a4%Z; 0x157a8%Z; 0x157ac%Z;
  0x157b0%Z; 0x157b4%Z; 0x157b8%Z; 0x157bc%Z; 0x157c0%Z; 0x157c4%Z; 0x157c8%Z; 0x157cc%Z; 0x157d0%Z; 0x157d4%Z; 0x157d8%Z; 0x157dc%Z;
  0x157e0%Z; 0x157e4%Z; 0x157e8%Z; 0x157ec%Z; 0x157f0%Z; 0x157f4%Z; 0x157f8%Z; 0x157fc%Z; 0x15800%Z; 0x15804%Z; 0x15808%Z; 0x1580c%Z;
  0x15810%Z; 0x15814%Z; 0x15818%Z; 0x1581c%Z; 0x15820%Z; 0x15824%Z; 0x15828%Z; 0x1582c%Z; 0x15830%Z; 0x15834%Z; 0x15838%Z; 0x1583c%Z;
  0x15840%Z; 0x15844%Z; 0x15848%Z; 0x1584c%Z; 0x15850%Z; 0x15854%Z; 0x15858%Z; 0x1585c%Z; 0x15860%Z; 0x15864%Z; 0x15868%Z; 0x1586c%Z;
  0x15870%Z; 0x15874%Z; 0x15878%Z; 0x1587c%Z; 0x15880%Z; 0x15884%Z; 0x15888%Z; 0x1588c%Z; 0x15890%Z; 0x15894%Z; 0x15898%Z; 0x1589c%Z;
  0x158a0%Z; 0x158a4%Z; 0x158a8%Z; 0x158ac%Z; 0x158b0%Z; 0x158b4%Z; 0x158b8%Z; 0x158bc%Z; 0x158c0%Z; 0x158c4%Z; 0x158c8%Z; 0x158cc%Z;
  0x158d0%Z; 0x158d4%Z; 0x158d8%Z; 0x158dc%Z; 0x158e0%Z; 0x158e4%Z; 0x158e8%Z; 0x158ec%Z; 0x158f0%Z; 0x158f4%Z; 0x158f8%Z; 0x158fc%Z;
  0x15900%Z; 0x15904%Z; 0x15908%Z; 0x1590c%Z; 0x15910%Z; 0x15914%Z; 0x15918%Z; 0x1591c%Z; 0x15920%Z; 0x15924%Z; 0x15928%Z; 0x1592c%Z;
  0x15930%Z; 0x15934%Z; 0x15938%Z; 0x1593c%Z; 0x15940%Z; 0x15944%Z; 0x15948%Z; 0x1594c%Z; 0x15950%Z; 0x15954%Z; 0x15958%Z; 0x1595c%Z;
  0x15960%Z; 0x15964%Z; 0x15968%Z; 0x1596c%Z; 0x15970%Z; 0x15974%Z; 0x15978%Z; 0x1597c%Z; 0x15980%Z; 0x15984%Z; 0x15988%Z; 0x1598c%Z;
  0x15990%Z; 0x15994%Z; 0x15998%Z; 0x1599c%Z; 0x159a0%Z; 0x159a4%Z; 0x159a8%Z; 0x159ac%Z; 0x159b0%Z; 0x159b4%Z; 0x159b8%Z; 0x159bc%Z;
  0x159c0%Z; 0x159c4%Z; 0x159c8%Z; 0x159cc%Z; 0x159d0%Z; 0x159d4%Z; 0x159d8%Z; 0x159dc%Z; 0x159e0%Z; 0x159e4%Z; 0x159e8%Z; 0x159ec%Z;
  0x159f0%Z; 0x159f4%Z; 0x159f8%Z; 0x159fc%Z; 0x15a00%Z; 0x15a04%Z; 0x15a08%Z; 0x15a0c%Z; 0x15a10%Z; 0x15ce4%Z; 0x15ce8%Z; 0x15cec%Z;
  0x15cf0%Z; 0x15cf4%Z; 0x15cf8%Z; 0x15cfc%Z; 0x15d00%Z; 0x15d04%Z; 0x15d08%Z; 0x15d0c%Z
].

Definition pinnedIndexInstructions : list (Z * isla_trace) :=
  omap (fun address =>
    option_map (fun trace => (address, trace))
      (IslaTraces.write_success_blocks.Index.lookup address))
    pinnedIndexAddresses.

Definition pinnedInstructions : list (Z * isla_trace) :=
  IslaTraces.decoder_00.instrs.instr_map ++
  IslaTraces.decoder_01.instrs.instr_map ++
  IslaTraces.decoder_02.instrs.instr_map ++
  IslaTraces.decoder_03.instrs.instr_map ++
  IslaTraces.decoder_04.instrs.instr_map ++
  IslaTraces.decoder_05.instrs.instr_map ++
  IslaTraces.decoder_06.instrs.instr_map ++
  IslaTraces.decoder_07.instrs.instr_map ++
  IslaTraces.decoder_08.instrs.instr_map ++
  IslaTraces.decoder_09.instrs.instr_map ++
  IslaTraces.decoder_10.instrs.instr_map ++
  IslaTraces.decoder_11.instrs.instr_map ++
  IslaTraces.decoder_12.instrs.instr_map ++
  IslaTraces.decoder_13.instrs.instr_map ++
  IslaTraces.decoder_14.instrs.instr_map ++
  IslaTraces.decoder_15.instrs.instr_map ++
  IslaTraces.decoder_16.instrs.instr_map ++
  IslaTraces.decoder_17.instrs.instr_map ++
  IslaTraces.decoder_18.instrs.instr_map ++
  IslaTraces.decoder_19.instrs.instr_map ++
  IslaTraces.decoder_20.instrs.instr_map ++
  IslaTraces.decoder_21.instrs.instr_map ++
  IslaTraces.decoder_22.instrs.instr_map ++
  IslaTraces.decoder_23.instrs.instr_map ++
  IslaTraces.decoder_24.instrs.instr_map ++
  IslaTraces.decoder_25.instrs.instr_map ++
  IslaTraces.decoder_26.instrs.instr_map ++
  IslaTraces.decoder_27.instrs.instr_map ++
  IslaTraces.decoder_28.instrs.instr_map ++
  IslaTraces.decoder_29.instrs.instr_map ++
  IslaTraces.decoder_30.instrs.instr_map ++
  IslaTraces.decoder_31.instrs.instr_map ++
  IslaTraces.decoder_32.instrs.instr_map ++
  IslaTraces.decoder_33.instrs.instr_map ++
  IslaTraces.decoder_34.instrs.instr_map ++
  IslaTraces.decoder_35.instrs.instr_map ++
  IslaTraces.decoder_36.instrs.instr_map ++
  IslaTraces.decoder_37.instrs.instr_map ++
  IslaTraces.decoder_38.instrs.instr_map ++
  IslaTraces.decoder_39.instrs.instr_map ++
  IslaTraces.decoder_40.instrs.instr_map ++
  IslaTraces.decoder_41.instrs.instr_map ++
  IslaTraces.decoder_42.instrs.instr_map ++
  IslaTraces.decoder_43.instrs.instr_map ++
  IslaTraces.decoder_44.instrs.instr_map ++
  IslaTraces.decoder_45.instrs.instr_map ++
  IslaTraces.decoder_46.instrs.instr_map ++
  IslaTraces.decoder_47.instrs.instr_map ++
  IslaTraces.decoder_48.instrs.instr_map ++
  IslaTraces.decoder_49.instrs.instr_map ++
  IslaTraces.decoder_50.instrs.instr_map ++
  IslaTraces.decoder_51.instrs.instr_map ++
  IslaTraces.decoder_52.instrs.instr_map ++
  IslaTraces.decoder_53.instrs.instr_map ++
  IslaTraces.decoder_54.instrs.instr_map ++
  IslaTraces.decoder_55.instrs.instr_map ++
  IslaTraces.decoder_56.instrs.instr_map ++
  IslaTraces.decoder_57.instrs.instr_map ++
  IslaTraces.decoder_58.instrs.instr_map ++
  IslaTraces.decoder_59.instrs.instr_map ++
  IslaTraces.decoder_60.instrs.instr_map ++
  IslaTraces.decoder_61.instrs.instr_map ++
  IslaTraces.decoder_62.instrs.instr_map ++
  IslaTraces.decoder_63.instrs.instr_map ++
  IslaTraces.decoder_64.instrs.instr_map ++
  IslaTraces.decoder_65.instrs.instr_map ++
  IslaTraces.decoder_66.instrs.instr_map ++
  IslaTraces.decoder_67.instrs.instr_map ++
  IslaTraces.decoder_68.instrs.instr_map ++
  IslaTraces.decoder_69.instrs.instr_map ++
  IslaTraces.decoder_70.instrs.instr_map ++
  IslaTraces.decoder_71.instrs.instr_map ++
  IslaTraces.decoder_72.instrs.instr_map ++
  IslaTraces.decoder_73.instrs.instr_map ++
  IslaTraces.decoder_74.instrs.instr_map ++
  IslaTraces.decoder_75.instrs.instr_map ++
  IslaTraces.decoder_76.instrs.instr_map ++
  IslaTraces.decoder_77.instrs.instr_map ++
  IslaTraces.decoder_78.instrs.instr_map ++
  IslaTraces.decoder_79.instrs.instr_map ++
  IslaTraces.decoder_80.instrs.instr_map ++
  IslaTraces.decoder_81.instrs.instr_map ++
  IslaTraces.decoder_82.instrs.instr_map ++
  IslaTraces.decoder_83.instrs.instr_map ++
  IslaTraces.decoder_84.instrs.instr_map ++
  IslaTraces.decoder_85.instrs.instr_map ++
  IslaTraces.decoder_86.instrs.instr_map ++
  IslaTraces.decoder_87.instrs.instr_map ++
  IslaTraces.decoder_88.instrs.instr_map ++
  IslaTraces.decoder_89.instrs.instr_map ++
  IslaTraces.decoder_90.instrs.instr_map ++
  IslaTraces.decoder_91.instrs.instr_map ++
  IslaTraces.decoder_92.instrs.instr_map ++
  IslaTraces.decoder_93.instrs.instr_map ++
  IslaTraces.decoder_94.instrs.instr_map ++
  IslaTraces.decoder_95.instrs.instr_map ++
  IslaTraces.decoder_96.instrs.instr_map ++
  IslaTraces.decoder_97.instrs.instr_map ++
  IslaTraces.decoder_98.instrs.instr_map ++
  IslaTraces.decoder_99.instrs.instr_map ++
  IslaTraces.decoder_100.instrs.instr_map ++
  IslaTraces.decoder_101.instrs.instr_map ++
  IslaTraces.decoder_102.instrs.instr_map ++
  IslaTraces.decoder_103.instrs.instr_map ++
  IslaTraces.decoder_104.instrs.instr_map ++
  IslaTraces.decoder_105.instrs.instr_map ++
  IslaTraces.decoder_106.instrs.instr_map ++
  IslaTraces.decoder_107.instrs.instr_map ++
  IslaTraces.decoder_108.instrs.instr_map ++
  IslaTraces.decoder_109.instrs.instr_map ++
  IslaTraces.decoder_110.instrs.instr_map ++
  IslaTraces.decoder_111.instrs.instr_map ++
  IslaTraces.decoder_112.instrs.instr_map ++
  IslaTraces.decoder_113.instrs.instr_map ++
  IslaTraces.decoder_114.instrs.instr_map ++
  IslaTraces.decoder_115.instrs.instr_map ++
  IslaTraces.decoder_116.instrs.instr_map ++
  IslaTraces.decoder_117.instrs.instr_map ++
  IslaTraces.decoder_118.instrs.instr_map ++
  IslaTraces.decoder_119.instrs.instr_map ++
  IslaTraces.decoder_120.instrs.instr_map ++
  IslaTraces.decoder_121.instrs.instr_map ++
  IslaTraces.decoder_122.instrs.instr_map ++
  IslaTraces.decoder_123.instrs.instr_map ++
  IslaTraces.decoder_124.instrs.instr_map ++
  IslaTraces.decoder_125.instrs.instr_map ++
  IslaTraces.decoder_126.instrs.instr_map ++
  IslaTraces.decoder_127.instrs.instr_map ++
  IslaTraces.decoder_128.instrs.instr_map ++
  IslaTraces.decoder_129.instrs.instr_map ++
  IslaTraces.decoder_130.instrs.instr_map ++
  IslaTraces.decoder_131.instrs.instr_map ++
  IslaTraces.decoder_132.instrs.instr_map ++
  IslaTraces.decoder_133.instrs.instr_map ++
  IslaTraces.decoder_134.instrs.instr_map ++
  IslaTraces.decoder_135.instrs.instr_map ++
  IslaTraces.decoder_136.instrs.instr_map ++
  IslaTraces.decoder_137.instrs.instr_map ++
  IslaTraces.decoder_138.instrs.instr_map ++
  IslaTraces.decoder_139.instrs.instr_map ++
  IslaTraces.decoder_140.instrs.instr_map ++
  IslaTraces.decoder_141.instrs.instr_map ++
  IslaTraces.decoder_142.instrs.instr_map ++
  IslaTraces.decoder_143.instrs.instr_map ++
  IslaTraces.decoder_144.instrs.instr_map ++
  IslaTraces.decoder_145.instrs.instr_map ++
  IslaTraces.decoder_146.instrs.instr_map ++
  IslaTraces.decoder_147.instrs.instr_map ++
  IslaTraces.decoder_148.instrs.instr_map ++
  IslaTraces.decoder_149.instrs.instr_map ++
  IslaTraces.decoder_150.instrs.instr_map ++
  IslaTraces.decoder_151.instrs.instr_map ++
  IslaTraces.decoder_152.instrs.instr_map ++
  IslaTraces.decoder_153.instrs.instr_map ++
  IslaTraces.decoder_154.instrs.instr_map ++
  IslaTraces.decoder_155.instrs.instr_map ++
  IslaTraces.decoder_156.instrs.instr_map ++
  IslaTraces.decoder_157.instrs.instr_map ++
  IslaTraces.decoder_158.instrs.instr_map ++
  IslaTraces.decoder_159.instrs.instr_map ++
  IslaTraces.decoder_160.instrs.instr_map ++
  IslaTraces.decoder_161.instrs.instr_map ++
  IslaTraces.decoder_162.instrs.instr_map ++
  IslaTraces.decoder_163.instrs.instr_map ++
  IslaTraces.decoder_164.instrs.instr_map ++
  IslaTraces.decoder_165.instrs.instr_map ++
  IslaTraces.decoder_166.instrs.instr_map ++
  IslaTraces.decoder_167.instrs.instr_map ++
  IslaTraces.decoder_168.instrs.instr_map ++
  IslaTraces.decoder_169.instrs.instr_map ++
  IslaTraces.decoder_170.instrs.instr_map ++
  IslaTraces.decoder_171.instrs.instr_map ++
  IslaTraces.decoder_172.instrs.instr_map ++
  IslaTraces.decoder_173.instrs.instr_map ++
  IslaTraces.decoder_174.instrs.instr_map ++
  IslaTraces.decoder_175.instrs.instr_map ++
  IslaTraces.decoder_176.instrs.instr_map ++
  IslaTraces.decoder_177.instrs.instr_map ++
  IslaTraces.decoder_178.instrs.instr_map ++
  IslaTraces.decoder_179.instrs.instr_map ++
  IslaTraces.decoder_180.instrs.instr_map ++
  IslaTraces.decoder_181.instrs.instr_map ++
  IslaTraces.decoder_182.instrs.instr_map ++
  IslaTraces.decoder_183.instrs.instr_map ++
  IslaTraces.decoder_184.instrs.instr_map ++
  IslaTraces.decoder_185.instrs.instr_map ++
  IslaTraces.decoder_186.instrs.instr_map ++
  IslaTraces.decoder_187.instrs.instr_map ++
  IslaTraces.decoder_188.instrs.instr_map ++
  IslaTraces.decoder_189.instrs.instr_map ++
  IslaTraces.decoder_190.instrs.instr_map ++
  IslaTraces.decoder_191.instrs.instr_map ++
  IslaTraces.decoder_192.instrs.instr_map ++
  IslaTraces.decoder_193.instrs.instr_map ++
  IslaTraces.decoder_194.instrs.instr_map ++
  IslaTraces.decoder_195.instrs.instr_map ++
  IslaTraces.decoder_196.instrs.instr_map ++
  IslaTraces.decoder_197.instrs.instr_map ++
  IslaTraces.decoder_198.instrs.instr_map ++
  IslaTraces.decoder_199.instrs.instr_map ++
  IslaTraces.decoder_200.instrs.instr_map ++
  IslaTraces.decoder_201.instrs.instr_map ++
  IslaTraces.decoder_202.instrs.instr_map ++
  IslaTraces.decoder_203.instrs.instr_map ++
  IslaTraces.decoder_204.instrs.instr_map ++
  IslaTraces.decoder_205.instrs.instr_map ++
  IslaTraces.decoder_206.instrs.instr_map ++
  IslaTraces.decoder_207.instrs.instr_map ++
  IslaTraces.decoder_208.instrs.instr_map ++
  IslaTraces.decoder_209.instrs.instr_map ++
  IslaTraces.decoder_210.instrs.instr_map ++
  IslaTraces.decoder_211.instrs.instr_map ++
  IslaTraces.decoder_212.instrs.instr_map ++
  IslaTraces.decoder_213.instrs.instr_map ++
  IslaTraces.decoder_214.instrs.instr_map ++
  IslaTraces.decoder_215.instrs.instr_map ++
  IslaTraces.decoder_216.instrs.instr_map ++
  IslaTraces.decoder_217.instrs.instr_map ++
  IslaTraces.decoder_218.instrs.instr_map ++
  IslaTraces.decoder_219.instrs.instr_map ++
  IslaTraces.decoder_220.instrs.instr_map ++
  IslaTraces.decoder_221.instrs.instr_map ++
  IslaTraces.decoder_222.instrs.instr_map ++
  IslaTraces.decoder_223.instrs.instr_map ++
  IslaTraces.decoder_224.instrs.instr_map ++
  IslaTraces.decoder_225.instrs.instr_map ++
  IslaTraces.decoder_226.instrs.instr_map ++
  IslaTraces.decoder_227.instrs.instr_map ++
  IslaTraces.decoder_228.instrs.instr_map ++
  IslaTraces.decoder_229.instrs.instr_map ++
  IslaTraces.decoder_230.instrs.instr_map ++
  IslaTraces.decoder_231.instrs.instr_map ++
  IslaTraces.decoder_232.instrs.instr_map ++
  IslaTraces.decoder_233.instrs.instr_map ++
  IslaTraces.decoder_234.instrs.instr_map ++
  IslaTraces.decoder_235.instrs.instr_map ++
  IslaTraces.decoder_236.instrs.instr_map ++
  IslaTraces.decoder_237.instrs.instr_map ++
  IslaTraces.decoder_238.instrs.instr_map ++
  IslaTraces.decoder_239.instrs.instr_map ++
  IslaTraces.decoder_240.instrs.instr_map ++
  IslaTraces.decoder_241.instrs.instr_map ++
  IslaTraces.decoder_242.instrs.instr_map ++
  IslaTraces.decoder_243.instrs.instr_map ++
  IslaTraces.decoder_244.instrs.instr_map ++
  IslaTraces.decoder_245.instrs.instr_map ++
  IslaTraces.decoder_246.instrs.instr_map ++
  IslaTraces.decoder_247.instrs.instr_map ++
  IslaTraces.decoder_248.instrs.instr_map ++
  IslaTraces.decoder_249.instrs.instr_map ++
  IslaTraces.decoder_250.instrs.instr_map ++
  IslaTraces.decoder_251.instrs.instr_map ++
  IslaTraces.decoder_252.instrs.instr_map ++
  IslaTraces.decoder_253.instrs.instr_map ++
  IslaTraces.decoder_254.instrs.instr_map ++
  IslaTraces.decoder_255.instrs.instr_map ++
  IslaTraces.decoder_256.instrs.instr_map ++
  IslaTraces.decoder_257.instrs.instr_map ++
  IslaTraces.decoder_258.instrs.instr_map ++
  IslaTraces.decoder_259.instrs.instr_map ++
  IslaTraces.decoder_260.instrs.instr_map ++
  IslaTraces.decoder_261.instrs.instr_map ++
  IslaTraces.decoder_262.instrs.instr_map ++
  IslaTraces.decoder_263.instrs.instr_map ++
  IslaTraces.decoder_264.instrs.instr_map ++
  IslaTraces.decoder_265.instrs.instr_map ++
  IslaTraces.decoder_266.instrs.instr_map ++
  IslaTraces.decoder_267.instrs.instr_map ++
  IslaTraces.decoder_268.instrs.instr_map ++
  IslaTraces.decoder_269.instrs.instr_map ++
  IslaTraces.decoder_270.instrs.instr_map ++
  IslaTraces.decoder_271.instrs.instr_map ++
  IslaTraces.decoder_272.instrs.instr_map ++
  IslaTraces.decoder_273.instrs.instr_map ++
  IslaTraces.decoder_274.instrs.instr_map ++
  IslaTraces.decoder_275.instrs.instr_map ++
  IslaTraces.decoder_276.instrs.instr_map ++
  IslaTraces.decoder_277.instrs.instr_map ++
  IslaTraces.startup.instrs.instr_map ++
  IslaTraces.main.instrs.instr_map ++
  IslaTraces.read_input.instrs.instr_map ++
  IslaTraces.allocator_get.instrs.instr_map ++
  IslaTraces.write_failure.instrs.instr_map ++
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
  IslaTraces.write_success_127.instrs.instr_map ++
  pinnedIndexInstructions.

Definition pinnedInstructionTable : gmap addr isla_trace :=
  <[ BV 64 0x14cb0 := IslaTraces.main.a14cb0.a14cb0 ]>
  (<[ BV 64 0x12168 := IslaTraces.decoder_00.a12168.a12168 ]>
    (list_to_map (List.map (fun item => (Z_to_bv 64 item.1, item.2))
      pinnedInstructions))).

Lemma pinned_main_instruction :
  pinnedInstructionTable !! BV 64 0x14cb0 =
    Some IslaTraces.main.a14cb0.a14cb0.
Proof. apply lookup_insert. Qed.

Lemma pinned_decoder_instruction :
  pinnedInstructionTable !! BV 64 0x12168 =
    Some IslaTraces.decoder_00.a12168.a12168.
Proof.
  unfold pinnedInstructionTable.
  rewrite lookup_insert_ne; last (vm_compute; congruence).
  apply lookup_insert.
Qed.
