# Proof starting point

Begin with `Contracts/Level1.v`.
Define each `IslarisContractResources` instance with its complete entry and exit resources.
Do not introduce a deeper contract hierarchy before a failed direct proof requires it.
Keep the `DecoderModel` binding as a visible conditional assumption.

Use the generated entry traces to test each function boundary first.
Then generate complete trace chunks for one Level 1 contract at a time.

The intended proof order is:

1. Prove each native Islaris state-correctness specification.
2. Prove each bounded instruction-path certificate.
3. Construct `IslarisLevel1ContractAssumptions` from the six results.
4. Prove `MainComplianceStatement` for the fixed bug list.
5. Derive `MainExactComplianceStatement` for selected safe inputs.

Do not use measured evidence as a premise.
Do not add a bug constructor during proof work without a separate review.
