Use the canonical emitters in `PACKET.json`.
The packet contains declaration templates and exact emitted examples.
The templates contain placeholders and are not standalone Rocq modules.

For each existential successor tuple:

1. Bind the exact target declaration source.
2. Bind the existing mapping fragment and its independent emitted-slot metadata.
3. Obtain source names and types from the declaration parser.
4. Obtain data names and types from the authenticated mapping emission.
5. Call `witness_data.witness_profile_metadata`.
6. Append its two records to the mapping module.
7. Add the direct `ZesuSsz.Automation.EntryWitnessProfile` import.

The exact function signature and every argument appear in `PACKET.json`.
`render_support.witness_mapping_source` already appends these records for generated data.
`source_witness_bindings.render_source_mapping` also emits the records for authenticated source plans.
Use that source emitter when witnesses come from source existentials or trace declarations.
It preserves their exact source identities.

Each profile record uses the same exact entry application and ordinary witness type.
Keep all entry parameters and the continuation `K`.
The declaration hash binds the source text that the emitter parses.
The mapping hash binds the mapping fragment before the appended metadata.
Use the emitter's fragment hash.
Do not hash the final module instead.

Preserve declaration order in both profile spines.
Each spine ends with `ZesuWitnessProfileEnd`.
The ordinary product ends with `unit`.
The existing selector reverses the data once.
The guard reverses only its metadata view.
Do not reverse the emitted names or values first.

The 5-slot and 7-slot examples preserve frozen mappings.
Their phase pointers bind the actual remaining slots.
They do not derive data names from the target.
The 11-slot examples show the complete source-capture interface.

Profile metadata does not establish a witness value or a semantic fact.
Report any missing mapping slot or source identity.
Do not infer a value from its type or tuple position.
Keep the readiness phase check and the existing selector.
Recompile declarations in the compatible bank.
Do not copy historical example objects.

`READER124` and `DECLARE123` prove source capture and typed-reader activation.
They do not prove the caller theorems.
The genuine rebuild binding remains `FINAL125-GENUINE-RESULT.json`.
The two caller138 searches remain separate from this packet.
