"""The protected PUBLIC decodeItem compliance theorems and their trust contexts.

tools/soundness_gate.py reads these two values. The October closure checker that
used to live here (native coverage rows, arm bindings, receipt verification) is
retired with the October proof stack; the soundness gate checks the PUBLIC closure.
"""

PUBLIC = {
    'decodeItemSelectedCompliance': 'ZesuSsz/Compliance/DecodeItemCompliance.v',
    'decodeItemSelectedComplianceRegisters': 'ZesuSsz/Compliance/DecodeItemCompositionalCompliance.v',
    'decodeItemSelectedComplianceCompositional': 'ZesuSsz/Compliance/DecodeItemCompositionalCompliance.v',
    'decodeItemGeneratedCompliance': 'ZesuSsz/Compliance/DecodeItemComplianceGenerated.v',
}
# These modules fix the claim and its signature. Entry modules may change.
PUBLIC_CONTEXTS = (
    'ZesuSsz/Contracts/Level1.v',
    'ZesuSsz/Contracts/RlpDecodeItemContract.v',
    'ZesuSsz/Compliance/KnownBugs.v',
    'ZesuSsz/Evidence/SignatureGates.v',
)
