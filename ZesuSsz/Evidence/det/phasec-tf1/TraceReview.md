# TF1 witness trace connection

The witness trace equality closes.
The direct segment proof remains open.
The proposed trace contains five bytes calls, three byte-list calls, and one integer call.
The existing witness uses `writeSuccessExactPostPayloadsAt` and `writeOutputPayloadsSpec`.
The connection must preserve `writeSuccessExactTailFirstBranchEvents` as the exit tail.

The source review identified these existing support lemmas:

- `exact_tail_payload_suffix` removes the main payload prefix.
- `writeSuccessNativeWithdrawalFragments_length` matches the withdrawal prefix length.
- `exact_byte_lists_model` supplies the three byte-list call models.
- `writeSuccessPrivatePublicBytes` restores each exact payload from its public observation.
- `writeOutputPayloadsSpec_app` composes exact payload specifications.

The first five count writes use each descriptor's size.
The observation encodes each payload's length.
The descriptor resources carry those five size equalities.
The byte-list resources carry each item's size equality.
The final integer call uses decoded tail word 6.
`writeSuccessNativeObservation` uses that same word for the chain ID.

No trace was regenerated.
No binary, generator, configuration, or existing trace changed.
No trace hypothesis was added to a theorem.


The focused MCP compilation passed for these lemmas:

- `tail_fields_witness_payload_suffix`: Closed under the global context.
- `tail_fields_witness_trace_connection`: Closed under the global context.
- `tail_fields_resource_size_facts`: Closed under the global context.

The final focused compilation took approximately 8.5 seconds.
The trace connection uses three recorded hand lines.
The size-fact proof uses five recorded hand lines.
The size-fact proof preserves all original payload resources.
The existing exit predicate stays unchanged.
Final `rocq_verify` passed. The root preview remains pending.

Final MCP verification passed with `assumptions: []`.
