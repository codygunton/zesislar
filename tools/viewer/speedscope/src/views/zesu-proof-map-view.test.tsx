import {
  authoringRegionDetail,
  proofBoundaryDetail,
  refinementNodeDetail,
  renderProofCfg,
  renderProofMap,
} from './zesu-proof-map-view'

// A proof map with one of everything the panels read: the coverage totals, two
// authoring states so the filter has something to remove, a Level 3 parent with
// one proved child and one unproved child, and all four graph columns.
function proofMap(): any {
  return {
    formalCoverage: {
      directPcCount: 40,
      boundaryRegionPcCount: 100,
      conditionalContractPcCount: 250,
      endpointPcCount: 500,
    },
    compilerProvenance: {state: 'same-ELF DWARF'},
    authoringRegions: [
      {
        id: 'region-proved',
        label: 'read_input',
        authoringState: 'proved',
        blocker: 'None: this leaf contract is proved unconditionally.',
        pcs: [1, 2, 3],
        boundaryIds: ['fn-0x10140'],
        evidence: 'captured',
        preparation: {
          liveRegisters: ['buffer = x10'],
          protectedMemory: ['stack'],
          prerequisites: ['aligned'],
          sourceIdentity: 'read_input',
        },
        templateMatches: [{name: 'loadStore', score: [3, 4], module: 'Motifs'}],
        starterProof: {trust: 'authoring suggestion', text: 'by decide'},
      },
      {
        id: 'region-open',
        label: 'ssz.decode',
        authoringState: 'contract_specified_assumption',
        blocker: 'Typed contract is specified.',
        boundaryInstructionCount: 5920,
      },
    ],
    boundaries: [
      {
        id: 'fn-0x10140',
        qualified: 'read_input',
        entryPc: 0x10140,
        ownedInstructionCount: 20,
        subtreeInstructionCount: 24,
        observedVectors: ['minimal'],
        observedExitTransitions: [[0x10150, 0x10154]],
        evidenceStatus: 'captured',
        contractStatus: 'specified_assumption',
        proofStatus: 'proved',
      },
    ],
    phases: [{id: 'phase-main', label: 'main', pcs: [1, 2]}],
    instructions: [
      {pc: 1, mnemonic: 'addi', operands: 'a0, a0, 1'},
      {pc: 2, mnemonic: 'ret', operands: ''},
    ],
    hLevel3Preparation: {
      summary: {
        level3ContractCount: 4,
        parentGlueInstructionCount: 271,
        parentGlueObligationCount: 22,
      },
      proofProgress: {directProofCount: 1, remainingContractCount: 3},
      parents: [
        {
          field: 'writeSuccessInt',
          stagingTheorem: 'resolve_writeSuccessInt',
          glueInstructionCount: 5,
          children: [
            {instanceId: 'a', qualified: 'a', proofStatus: 'proved', contractStatus: 'specified'},
            {instanceId: 'b', qualified: 'b', proofStatus: 'not_started', contractStatus: 'open'},
          ],
          glueObligations: [
            {
              entryPc: 0x1234,
              instructionCount: 3,
              preferredStrategy: {composition: [{api: {name: 'step'}}]},
            },
          ],
        },
      ],
    },
    refinementGraph: {
      nodes: [
        {
          id: 'spec',
          column: 0,
          kind: 'specification',
          label: 'EVM-Sail reference',
          status: 'artifact',
          instructionCount: 0,
        },
        {
          id: 'contract-fn-0x10140',
          column: 1,
          kind: 'level1Contract',
          label: 'read_input',
          status: 'proved',
          boundaryId: 'fn-0x10140',
          instructionCount: 20,
          level0UseStatus: 'consumed',
          source: 'deps/zesu/src/zkvm/extern_io.zig',
        },
        {
          id: 'glue-main',
          column: 1,
          kind: 'parentGlue',
          label: 'main parent-owned glue',
          status: 'proved',
          proofStatus: 'proved',
          phase: 'phase-main',
          instructionCount: 24,
          provedInstructionCount: 24,
          absorbedInlineInstructionCount: 2,
        },
        {
          id: 'conversion',
          column: 2,
          kind: 'conversion',
          label: 'exportedContracts_of_level1',
          status: 'proved',
          proofStatus: 'proved',
        },
        {
          id: 'root',
          column: 3,
          kind: 'parent',
          label: 'root_compliance',
          status: 'conditionally_proven',
          proofStatus: 'conditionally_proven',
        },
      ],
      edges: [
        {source: 'spec', target: 'contract-fn-0x10140', kind: 'call'},
        {source: 'glue-main', target: 'conversion', kind: 'return'},
        {source: 'conversion', target: 'root', kind: 'call'},
      ],
    },
  }
}

describe('proof map panel', () => {
  it('reports the coverage totals', () => {
    const html = renderProofMap(proofMap(), 'all')
    expect(html).toContain('40/100')
    expect(html).toContain('100/500')
    expect(html).toContain('250/500')
    expect(html).toContain('same-ELF DWARF')
  })

  it('offers a filter per authoring state and shows every region', () => {
    const html = renderProofMap(proofMap(), 'all')
    expect(html).toContain('data-filter="all"')
    expect(html).toContain('data-filter="proved"')
    expect(html).toContain('data-filter="contract_specified_assumption"')
    expect(html).toContain('data-region="region-proved"')
    expect(html).toContain('data-region="region-open"')
  })

  it('keeps only the filtered regions', () => {
    const html = renderProofMap(proofMap(), 'proved')
    expect(html).toContain('data-region="region-proved"')
    expect(html).not.toContain('data-region="region-open"')
  })

  it('reports Level 3 preparation per parent', () => {
    const html = renderProofMap(proofMap(), 'all')
    expect(html).toContain('1/4 child proofs complete')
    expect(html).toContain('writeSuccessInt')
    expect(html).toContain('1/2 child proofs')
    expect(html).toContain('resolve_writeSuccessInt')
    expect(html).toContain('0x1234: 3 steps')
  })

  it('escapes text that would otherwise close a tag', () => {
    const map = proofMap()
    map.authoringRegions[0].label = '<script>x</script>'
    expect(renderProofMap(map, 'all')).not.toContain('<script>')
  })
})

describe('refinement dependency graph', () => {
  it('draws every node and edge', () => {
    const svg = renderProofCfg(proofMap())
    for (const id of ['spec', 'contract-fn-0x10140', 'glue-main', 'conversion', 'root']) {
      expect(svg).toContain(`data-graph-id="${id}"`)
    }
    expect(svg.match(/class="cfg-link/g)!.length).toBe(3)
    expect(svg).toContain('1. reference semantics')
    expect(svg).toContain('4. compliance theorem')
  })

  it('describes each node by its own kind', () => {
    const svg = renderProofCfg(proofMap())
    expect(svg).toContain('24/24 glue instructions proved')
    expect(svg).toContain('consumed by Level 0')
    expect(svg).toContain('proof conditionally proven')
  })

  it('shows a status for the node that carries no proof status', () => {
    // The reference-semantics node states an artifact, not a proof. Reading
    // `proofStatus` there is what crashed the viewer this replaced.
    const svg = renderProofCfg(proofMap())
    expect(svg).toContain('artifact')
  })
})

describe('proof map details', () => {
  it('separates an authoring suggestion from proof', () => {
    const detail = authoringRegionDetail(proofMap(), 'region-proved')!
    expect(detail.name).toBe('read_input')
    expect(detail.html).toContain('authoring suggestion — not proof')
    expect(detail.html).toContain('buffer = x10')
    expect(detail.html).toContain('loadStore')
    expect(detail.html).toContain('by decide')
  })

  it('reports a boundary instance', () => {
    const detail = proofBoundaryDetail(proofMap(), 'fn-0x10140')!
    expect(detail.html).toContain('0x10140')
    expect(detail.html).toContain('20 owned; 24 execution closure')
    expect(detail.html).toContain('0x10150 → 0x10154')
    expect(detail.html).toContain('specified assumption')
  })

  it('routes a contract node to its boundary', () => {
    const detail = refinementNodeDetail(proofMap(), 'contract-fn-0x10140')!
    expect(detail.sub).toBe('selected Level 1 instance')
  })

  it('lists the instructions a glue obligation owns', () => {
    const detail = refinementNodeDetail(proofMap(), 'glue-main')!
    expect(detail.html).toContain('24/24 instructions kernel-linked')
    expect(detail.html).toContain('0x1  addi')
  })

  it('names the role of the conversion and the compliance theorem', () => {
    expect(refinementNodeDetail(proofMap(), 'conversion')!.html).toContain(
      'Level1ContractAssumptions',
    )
    expect(refinementNodeDetail(proofMap(), 'root')!.html).toContain('compliance theorem')
  })
})
