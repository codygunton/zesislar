The OptionalU64 and ByteLists adapters state exact payload events.
Rocq MCP verified both adapters with no assumptions.
The caller probes use diagnostic entries from the earlier measurement table.
Those entries do not establish derivation from complete native predecessor poststates.
The diagnostic handoffs at 150f0, 15700, and 159b0 compile without assumptions.
The 159b0 handoff also passes rocq_verify.
These diagnostic proofs do not establish the Level 1 caller chain.
The normalized 15700 frame contains disjoint stack regions.
All captures from the earlier overlapping frame are invalid.
The shared witness rules require actual owned resources and complete trace proofs.
The trace refinement rule uses the upstream contravariant spec_trace_mono rule.
All 24 focused witness tests pass through Rocq MCP.
The tests reject absent ownership, incomplete traces, different exact payloads, invalid array bounds, and unresolved indices.
The native 15930 and Optional159bc entries need complete predecessor captures.
The origin 159a0 poststate retains abstract P and cannot supply the complete Optional frame.
