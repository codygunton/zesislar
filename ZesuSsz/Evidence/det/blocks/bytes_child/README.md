Eight bytes callers compile with closed assumptions at root 05ce8cd5.

The closed blocks are 151b4, 158e0, 158f0, 15900, 15910, 15920, 15980, and 1571c. Their proofs use only zesu_block. Rocq MCP compiled all entries, captured successors, and concrete blocks. Rocq MCP verify accepted all eight proofs with no assumptions.

Entry traces use the exact length and payload events over entry binders. Entries retain the captured words and complete register file. Callee scratch remains 48 bytes. The successor generator preserves register values that memory or entry parameters constrain.

The 151b4 proof took 2.726 + 0.428 tactic seconds. The other proofs took 3.082 to 5.868 tactic seconds. These figures measure tactics, not complete compiler time.

14eb8 lacks a captured entry. The Finish.v priority correction closes 1571c with its complete root event pair. Its tactic took 7.16 seconds.

The inputs directory contains each block entry and its captured successor. The names identify distinct states at shared addresses. tools/block/gen_block.py generated the committed modules through state_source and generate.
