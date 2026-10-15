The call instruction starts at 0x800d62b4.
Its containing block starts at 0x800d6274.
Its callee starts at 0x800d6960.
Its return site is 0x800d62b8.
The external table premise contains the complete compositional entry and return continuation.
The generator must not substitute the legacy exit or infer a contract from the target address.

Let S denote the caller entry stack pointer.
The callee receives sp=S-96, output=S-88, input=I, and input length=N.
Its x1 holds 0x800d62b8.
Its saved x8 value is S.
Its preserved x9 is the caller result pointer.
Its preserved x18 is the caller slice pointer.
Its preserved x19 is I.
Its preserved x20 is N.
Its x21 through x27 retain their caller entry values.
The exact input-end value remains part of the system-register resource.

The callee owns the whole input, the 40-byte output array, and the separate callee 16-byte frame.
The caller frames its 16-byte slice, 16-byte result, 8-byte padding, and 48-byte saved array array.
The caller 96-byte frame remains distinct from the separate callee 16-byte frame.
The callee returns fifteen caller-saved registers with existential values.
It preserves twelve callee-saved values and the stack pointer.
The return continuation must retain the exact output witness and before-image meaning relation.
It must not assume status, tag, payload length, or success acceptance before block 62b8.
The meaning remains DecodeMeaningModuloKnownBugs.

The existing theorem proves full compositional correctness.
This packet supplies a source-checked interface description.
It proves no new table-installation or caller-resource entailment.
The caller stack views and initialized before-image witness remain unproved.
The register flattening, output-fact packaging, and continuation framing remain unproved.
The generic boxed-entry installation also remains unproved in this packet.
No new premise enters the production contract.
No proof, compilation, or native run occurred.
Level1.v and IslarisContractCorrect remain unchanged.
Calls.v already declares Global Typeclasses Opaque machine_call machine_call_ret zesu_call.
The direct instr_pre route does not unfold zesu_call.
