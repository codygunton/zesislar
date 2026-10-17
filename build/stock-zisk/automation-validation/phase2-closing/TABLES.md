# Phase 2 closing tables: free

The holdout stays at 0/43. The best experimental training arm verified 16/43.
Training 4 verified 12/43 in both arms. The final candidate has no recorded result.

This report uses only the owner metrics and issue 13. It adds no proof, native run, or measurement.
A `null` cell means the allowed records supply no value.

## Recorded runs

F means the frozen EntryIntro, MaskNormalizer-Z, MaskNormalizer-bv, and ConjunctMatch rules.
Automation.Approved is imported. ReturnRoute, FinishFacts, and MemoryAccess stay inactive in that frozen set.
OFF and ON name comparison arms. They do not state merge status.

| Run or validation stage | Exact Root / source limit | Ruleset and changed scope | Predicted closures | Interactive closures | VERIFIED closures | Open blocks / pending validation | Auto controls | Evidence |
|---|---|---|---:|---:|---:|---|---|---|
|holdout724|e8131be2 (full hash: null)|Frozen EntryIntro + MaskNormalizer-Z + MaskNormalizer-bv + ConjunctMatch. Automation.Approved imported. ReturnRoute, FinishFacts, MemoryAccess inactive.|12|null|0|43|null|[#13:6209189220](https://github.com/codygunton/zesislar/issues/13#issuecomment-6209189220)|
|training1-758|25695558 (full hash: null)|Frozen rules unchanged. fresh successor binders and twelve introduction bundles.|26|null|0|43|null|[#13:6212028138](https://github.com/codygunton/zesislar/issues/13#issuecomment-6212028138) [#13:6212595451](https://github.com/codygunton/zesislar/issues/13#issuecomment-6212595451)|
|training2-805|3c8ab7b0f769176f509e16824faf675adef3674b|Frozen rules unchanged. register-style contracts and candidate equation. No normalization rule.|26|12|0|31 residual; 12 interactive closures await validation|null|[#13:6216737745](https://github.com/codygunton/zesislar/issues/13#issuecomment-6216737745) [#13:6216961043](https://github.com/codygunton/zesislar/issues/13#issuecomment-6216961043) [#13:6217323866](https://github.com/codygunton/zesislar/issues/13#issuecomment-6217323866)|
|training2-validation810|3c8ab7b0f769176f509e16824faf675adef3674b|Same training2 proof statements. Sets/call.vo loadpath repaired.|26|12|12|31|null|[#13:6219363359](https://github.com/codygunton/zesislar/issues/13#issuecomment-6219363359) [#13:6216961043](https://github.com/codygunton/zesislar/issues/13#issuecomment-6216961043)|
|training3-854-OFF|3aebfa260c6a38ef1abc9eae5ea4b342410de422|Frozen rules plus registered value bounds. whole EncodingNormalization switch OFF.|12|12|6|31 residual; 6 interactive closures await validation|9/9 verified|[#13:6219363359](https://github.com/codygunton/zesislar/issues/13#issuecomment-6219363359) [#13:6220748998](https://github.com/codygunton/zesislar/issues/13#issuecomment-6220748998)|
|training3-854-ON|3aebfa260c6a38ef1abc9eae5ea4b342410de422|Frozen rules plus registered value bounds. EncodingNormalization switch ON (candidate).|40|16|8|27 residual; 8 interactive closures await validation|7/9 verified; failed: 800d69e0, 800d6a6c|[#13:6219363359](https://github.com/codygunton/zesislar/issues/13#issuecomment-6219363359) [#13:6220748998](https://github.com/codygunton/zesislar/issues/13#issuecomment-6220748998)|
|training3-uncapped872-OFF|3aebfa260c6a38ef1abc9eae5ea4b342410de422|Same candidate/proof scope. Tool-side compilation timeouts removed. no new native comparison.|12|null|12|31|No new result. Earlier OFF 9/9, ON 7/9 remain.|[#13:6227257551](https://github.com/codygunton/zesislar/issues/13#issuecomment-6227257551) [#13:6219363359](https://github.com/codygunton/zesislar/issues/13#issuecomment-6219363359)|
|training3-uncapped872-ON|3aebfa260c6a38ef1abc9eae5ea4b342410de422|Same candidate/proof scope. Tool-side compilation timeouts removed. no new native comparison.|40|null|16|27|No new result. Earlier OFF 9/9, ON 7/9 remain.|[#13:6227257551](https://github.com/codygunton/zesislar/issues/13#issuecomment-6227257551) [#13:6219363359](https://github.com/codygunton/zesislar/issues/13#issuecomment-6219363359)|
|training4-995-OFF|0bf4b23c2e99e93312bc05243a48657c3992780a|Candidate includes conditional ite-form leaf facts. Whole encoding switch OFF.|12|null|12|31|9/9 verified; largest CPU change +4.94% (arm split not recorded)|[#13:6227257551](https://github.com/codygunton/zesislar/issues/13#issuecomment-6227257551) [#13:6228963505](https://github.com/codygunton/zesislar/issues/13#issuecomment-6228963505)|
|training4-995-ON|0bf4b23c2e99e93312bc05243a48657c3992780a|Candidate includes conditional ite-form leaf facts. Repaired goal-only keyed encoding switch ON.|30|null|12|31|9/9 verified; largest CPU change +4.94% (arm split not recorded)|[#13:6227257551](https://github.com/codygunton/zesislar/issues/13#issuecomment-6227257551) [#13:6228963505](https://github.com/codygunton/zesislar/issues/13#issuecomment-6228963505)|
|FINAL-candidate-OFF|not run|null|null|null|null|null|null|Training5 cancelled|
|FINAL-candidate-ON|not run|null|null|null|null|null|null|Training5 cancelled|

The 805 row preserves the initial zero VERIFIED closures. Its twelve interactive closures become VERIFIED only at validation 810.
The uncapped supplement validates existing training 3 closures. It is not another native comparison.
Training 3 initially had fourteen pending compilations. Their compiler costs were 7.7–24.1 CPU seconds after the tool-side timeout was removed.
F50 first recorded ON 15 verified plus one pending. The final metric and prediction comment later record ON 16 verified.
Training 3 ON retains two Auto regressions. The supplement does not erase them.
The holdout and training 1 sources give only Root prefixes. This report does not invent full hashes.

## Interface text for free

Physical line totals below measure per-function interface text. They do not measure handwritten block proof lines.
Generic automation text is outside this total. A larger interface does not itself establish a closure benefit.

| Recorded checkpoint | Interface lines | Change from previous checkpoint | Count expansion | Net change within inherited scope | What the change supplied / measured limit | Evidence |
|---|---:|---:|---:|---:|---|---|
|983|983|null|null|null|Initial pre-run contracts 571, introductions 113, exit meanings 57, registrations 131, generator JSON 111. No native benefit measured by this count.|[#13:6184742238](https://github.com/codygunton/zesislar/issues/13#issuecomment-6184742238)|
|1105|1105|122|0|122|Exit meanings +52 and registrations +70. The integrated contract/data package exists; the later holdout still verifies 0/43.|[#13:6186102018](https://github.com/codygunton/zesislar/issues/13#issuecomment-6186102018) Metrics `/functions/alt_fl_alloc.free/interface_lines_prerun`.|
|1621|1621|516|0|516|Twelve keyed leaf/class introductions address the omitted data route. Training 1 still verifies 0/43; generator repair also changed that run.|[#13:6210027851](https://github.com/codygunton/zesislar/issues/13#issuecomment-6210027851) [#13:6212595451](https://github.com/codygunton/zesislar/issues/13#issuecomment-6212595451) Metrics `/functions/alt_fl_alloc.free/interface_lines_training`.|
|11040|11040|9419|9392|27|Full counting adds 9392 previously excluded lines. The inherited scope adds 27 net lines. Register bounds and candidate facts accompany 12 verified class closures. Fourteen range blocks remain open. These sources do not name each added file.|[#13:6216737745](https://github.com/codygunton/zesislar/issues/13#issuecomment-6216737745) [#13:6217323866](https://github.com/codygunton/zesislar/issues/13#issuecomment-6217323866) Metrics `/functions/alt_fl_alloc.free/interface_lines_register_bounds`.|
|11135|11135|95|0|95|The value-bound hints enter both training 3 arms. OFF keeps 12 verified closures. ON reaches 16 after validation. Two Auto controls regress. The records do not isolate the benefit of these 95 lines.|[#13:6219363359](https://github.com/codygunton/zesislar/issues/13#issuecomment-6219363359) Metrics `/functions/alt_fl_alloc.free/interface_lines_value_bounds`.|
|11306|11306|171|0|171|The conditional ite-form facts support the keyed repair comparison. Training 4 verifies 12 closures in each arm. No leaf closure gain occurs.|[#13:6226480623](https://github.com/codygunton/zesislar/issues/13#issuecomment-6226480623) [#13:6227257551](https://github.com/codygunton/zesislar/issues/13#issuecomment-6227257551) [#13:6228963505](https://github.com/codygunton/zesislar/issues/13#issuecomment-6228963505) Metrics `/functions/alt_fl_alloc.free/interface_lines_ite_facts`.|
|11307|11307|1|0|1|The own-function umbrella exports the existing FreeSelected module. The count adds one line at cp-av-free-own-umbrella (1a4e2008). No isolated closure benefit is measured.| Metrics `/functions/alt_fl_alloc.free/interface_lines_own_umbrella`.|
|FINAL candidate|null|null|null|null|FINAL candidate: not run. Training5 was cancelled.|null|

The 11040 fully counted scope includes an inherited-scope total of 1648.
The count expansion is 11040 − 1648 = 9392 lines.
The inherited scope changed by 1648 − 1621 = 27 net lines.
Thus the apparent 9419-line increase does not represent 9419 newly written lines.
The generator category changed from 111 to 9503 counted lines. The difference also equals 9392.
The allowed records do not identify every file responsible for this expansion.

## Preserved defects and limits

- **706/F39 — Void startup:** Automation.Approved was omitted; zero machine instructions. This is not the recorded holdout724. Source: metrics findingsF39/F41; issue6209189220.
- **797/798 — Descriptor validation:** Zero native arms/tactics. Command799 corrects only descriptor/output paths. Source: issue6216961043.
- **805 to810 — Compilation environment:** Twelve interactive closures awaited Sets/call.vo loadpath repair. 810 verifies those statements with assumptions[]. Source: metrics training_run_2; issue6217323866/6219363359.
- **854 to uncapped872 — Tool-side compile timeouts:** OFF 6 / ON 8 pending compilation initially. Uncapped compiler CPU 7.7..24.1s. Final OFF 12 / ON 16 verified. No native rerun is inferred. Source: metrics training_run_3/uncapped_supplement.
- **training4 startup — Admission/launcher defects:** One admission deadlock and two launcher-packaging defects precede the isolated-writer restart. They have zero proof calls.995 is separate. Source: issue6228413689.

The stale top-level `free.spent=false` flag does not override the explicit spent holdout result.
The initial arithmetic-only explanation was qualified by later contract, introduction, and successor-binder findings.
This report does not infer a new finisher transition from a closed theorem.
The final candidate comparison did not run. Training5 was cancelled.
Numerical fields remain null because no measurement exists.
Run4 is final. Accepted best training has 12 verified closures.
Run3 ON16 remains unmerged diagnostic evidence with two Auto regressions.
Raw source snapshots and hashes stay in the untracked checkpoint package.
