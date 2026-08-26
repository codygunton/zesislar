import {h} from 'preact'
import {useCallback, useEffect, useRef, useState} from 'preact/hooks'
import {useTheme} from './themes/theme'
import {coveredBorderColor} from './themes/proof-palette'

// The proof map, the refinement dependency graph, the authoring cards, and the
// Level 3 preparation cards, ported from the D3 binary-regions viewer. The
// markup and the wording are the viewer's, because the claims they separate —
// machine structure, kernel-checked proof connection, and untrusted authoring
// suggestion — must keep reading the same.

const PROOF_MAP_URL = 'proof-map.json'

const esc = (value: unknown): string =>
  String(value).replace(/[&<>]/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;'})[c] as string)

const hex = (value: number): string => `0x${Number(value).toString(16)}`

interface Detail {
  name: string
  sub: string
  html: string
}

function statusColors(): Record<string, [string, string]> {
  return {
    local: ['#a8e6b8', '#67b77d'],
    proved: ['#a8e6b8', '#67b77d'],
    conditionally_proven: ['#d8e7a8', '#d0b253'],
    proof_in_progress: ['#ffe39a', '#d0b253'],
    contract_preliminary_shape: ['#ffe39a', '#d0b253'],
    contract_specified_assumption: ['#f4c4a3', '#d0b253'],
    contract_consumed: ['#f4c4a3', '#d0b253'],
    semantic_assumption: ['#f4c4a3', '#d0b253'],
    artifact: ['#f3aaaa', '#c96f6f'],
    contract_not_specified: ['#f3aaaa', '#c96f6f'],
    invalid_target_model: ['#f3aaaa', '#c96f6f'],
    proof_not_started: ['#f3aaaa', '#c96f6f'],
    not_started: ['#f3aaaa', '#c96f6f'],
  }
}

export function renderProofCfg(map: any): string {
  const graph = map.refinementGraph
  const groups = new Map<number, any[]>([0, 1, 2, 3].map(column => [column, [] as any[]]))
  graph.nodes.forEach((node: any) => groups.get(node.column)!.push(node))
  groups.forEach(nodes =>
    nodes.sort(
      (a: any, b: any) =>
        (a.phase || '').localeCompare(b.phase || '') || a.label.localeCompare(b.label),
    ),
  )
  const laneW = 300
  const nodeH = 42
  const nodeW = 250
  const top = 52
  const gap = 52
  const width = laneW * 4
  const height = top + Math.max(...[...groups.values()].map(x => x.length)) * gap + 24
  const positions = new Map<string, any>()
  for (const [column, nodes] of groups) {
    const offset = (height - top - nodes.length * gap) / 2
    nodes.forEach((node: any, row: number) =>
      positions.set(node.id, {
        x: column * laneW + 24,
        y: top + offset + row * gap,
        w: nodeW,
        h: nodeH,
        node,
      }),
    )
  }
  const colors = statusColors()
  const short = (s: string) => (s.length > 34 ? s.slice(0, 32) + '…' : s)
  const titles = [
    'reference semantics',
    'Level 1 contracts + Level 0 glue',
    'refinement theorem',
    'compliance theorem',
  ]
  const columns = titles
    .map(
      (title, i) => `<rect class="cfg-column" x="${i * laneW + 4}" y="4" width="${
        laneW - 8
      }" height="${height - 8}" rx="6"/>
    <text class="cfg-column-title" x="${i * laneW + 16}" y="25">${i + 1}. ${esc(title)}</text>`,
    )
    .join('')
  const edges = graph.edges
    .map((edge: any) => {
      const a = positions.get(edge.source)
      const b = positions.get(edge.target)
      if (!a || !b) return ''
      const x1 = a.x + a.w
      const y1 = a.y + a.h / 2
      const x2 = b.x
      const y2 = b.y + b.h / 2
      const mx = (x1 + x2) / 2
      return `<path class="cfg-link ${edge.kind}" marker-end="url(#cfg-arrow)" d="M${x1},${y1} C${mx},${y1} ${mx},${y2} ${x2},${y2}"><title>${edge.kind}</title></path>`
    })
    .join('')
  const nodes = [...positions.values()]
    .map(({x, y, w, h, node}) => {
      const [fill, stroke] = colors[node.status] || colors.artifact
      const sub =
        node.kind === 'parentGlue'
          ? `${node.provedInstructionCount}/${node.instructionCount} glue instructions proved`
          : node.kind === 'level1Contract'
            ? `${node.instructionCount} instructions · ${
                node.level0UseStatus === 'consumed' ? 'consumed by Level 0; ' : ''
              }machine proof not started`
            : // The reference-semantics node states an artifact, not a proof, so
              // it carries a status and no proof status.
              node.proofStatus
              ? `proof ${node.proofStatus.replaceAll('_', ' ')}`
              : `${node.status.replaceAll('_', ' ')}`
      return `<g data-graph-id="${esc(
        node.id,
      )}"><rect class="cfg-node-rect" x="${x}" y="${y}" width="${w}" height="${h}" fill="${fill}" stroke="${stroke}"><title>${esc(
        node.label,
      )}</title></rect>
      <text class="cfg-node-label" x="${x + 7}" y="${y + 16}">${esc(
        short(node.label),
      )}</text><text class="cfg-node-sub" x="${x + 7}" y="${y + 31}">${esc(sub)}</text></g>`
    })
    .join('')
  return `<svg viewBox="0 0 ${width} ${height}" width="${width}" height="${height}"><defs><marker id="cfg-arrow" markerWidth="6" markerHeight="6" refX="5" refY="3" orient="auto"><path d="M0,0 L6,3 L0,6 Z" fill="#657287"/></marker></defs>${columns}${edges}${nodes}</svg>`
}

export function renderProofMap(map: any, filter: string): string {
  const coverage = map.formalCoverage
  const visibleRegions = map.authoringRegions.filter(
    (region: any) => filter === 'all' || region.authoringState === filter,
  )
  const stat = (label: string, value: number, denominator: number, color: string) =>
    `<div class="proof-stat"><small>${esc(label)}</small><b>${value}/${denominator}</b>
    <div class="meter"><i style="width:${
      (value / denominator) * 100
    }%;background:${color}"></i></div></div>`
  const regions = visibleRegions
    .map(
      (region: any) => `<div class="author-card ${esc(region.authoringState)}"
      data-region="${esc(region.id)}"><b>${esc(region.label)}</b>
      <small>${esc(region.authoringState)} · ${
        (region.pcs || []).length || region.boundaryInstructionCount || 0
      } instructions</small>
      <div>${esc(region.blocker)}</div></div>`,
    )
    .join('')
  const l3 = map.hLevel3Preparation
  const l3Panel = !l3
    ? ''
    : `<div class="proof-tools"><b>hLevel3 preparation</b>
      <span class="muted">${l3.proofProgress.directProofCount}/${
        l3.summary.level3ContractCount
      } child proofs complete · ${l3.proofProgress.remainingContractCount} contracts remain · ${
        l3.summary.parentGlueInstructionCount
      } parent-glue instructions · ${
        l3.summary.parentGlueObligationCount
      } guided fragments</span></div>
    <div class="proof-grid">${l3.parents
      .map((parent: any) => {
        const proved = parent.children.filter((child: any) => child.proofStatus === 'proved').length
        return `<div class="author-card ${
          proved === parent.children.length ? 'proved' : 'contract_specified_assumption'
        }">
      <b>${esc(parent.field)}</b><small>${proved}/${parent.children.length} child proofs · ${
        parent.glueInstructionCount
      } glue instructions</small>
      <div>${esc(parent.stagingTheorem)} · ${parent.glueObligations.length} guided fragments</div>
      <details><summary>proof preparation</summary><div>${parent.children
        .map(
          (child: any) =>
            `${child.proofStatus === 'proved' ? '✓' : '○'} ${esc(
              child.qualified || child.instanceId,
            )}: ${esc(child.contractStatus)}${
              child.proofTheorem ? ` · ${esc(child.proofTheorem)}` : ''
            }`,
        )
        .join('<br>')}</div>
      <div>${parent.glueObligations
        .map(
          (item: any) =>
            `${hex(item.entryPc)}: ${item.instructionCount} steps · ${
              item.preferredStrategy.composition.map((x: any) => esc(x.api.name)).join(', ') ||
              'explicit composition'
            }`,
        )
        .join('<br>')}</div></details></div>`
      })
      .join('')}</div>`
  return `<div class="proof-summary">
      ${stat(
        'directly discharged PCs',
        coverage.directPcCount,
        coverage.boundaryRegionPcCount,
        '#a8e6b8',
      )}
      ${stat(
        'proved boundary region',
        coverage.boundaryRegionPcCount,
        coverage.endpointPcCount,
        '#7fcf92',
      )}
      ${stat(
        'conditional contract region',
        coverage.conditionalContractPcCount,
        coverage.endpointPcCount,
        '#ffe39a',
      )}</div>
    <div class="trust-legend"><span><i style="background:#a8e6b8"></i>formal local</span>
      <span><i style="background:#f3aaaa"></i>production ELF only</span>
      <span><i style="background:#ffe39a"></i>authoring suggestion</span>
      <span>LLVM IR: ${esc(map.compilerProvenance.state)}</span></div>
    <div class="proof-tools"><b>authoring regions</b>
      ${['all', ...new Set(map.authoringRegions.map((row: any) => row.authoringState))]
        .map(
          value =>
            `<button data-filter="${value}" ${filter === value ? 'disabled' : ''}>${String(value)
              .split('_')
              .join(' ')}</button>`,
        )
        .join('')}</div>
    <div class="proof-grid">${regions}</div>${l3Panel}<div class="proof-tools"><b>Refinement dependency graph</b>
      <span class="muted">selected contracts + parent-owned glue instructions → parent contract</span></div>
    <div class="cfg-canvas" id="proof-cfg">${renderProofCfg(map)}</div>`
}

export function authoringRegionDetail(map: any, id: string): Detail | null {
  const region = map.authoringRegions.find((row: any) => row.id === id)
  if (!region) return null
  const matches =
    (region.templateMatches || [])
      .map(
        (match: any) =>
          `${esc(match.name)} · score ${esc(match.score.join('/'))}<br><span class="muted">${esc(
            match.module,
          )}</span>`,
      )
      .join('<br>') || 'none'
  const prep = region.preparation || {}
  let html = `<div class="kv"><span>trust track</span><span>authoring suggestion — not proof</span>
    <span>state</span><span>${esc(region.authoringState)}</span><span>blocker</span><span>${esc(
      region.blocker,
    )}</span>
    <span>boundary IDs</span><span>${esc(
      (region.boundaryIds || []).join(', ') || 'parent-owned',
    )}</span>
    <span>empirical evidence</span><span>${esc(region.evidence || 'not attached')}</span>
    <span>live registers</span><span>${esc((prep.liveRegisters || []).join(', ') || 'none')}</span>
    <span>protected memory</span><span>${esc(
      (prep.protectedMemory || []).join('; ') || 'none',
    )}</span>
    <span>prerequisites</span><span>${esc((prep.prerequisites || []).join('; ') || 'none')}</span>
    <span>source identity</span><span>${esc(prep.sourceIdentity || 'unknown')}</span>
    <span>template matches</span><span>${matches}</span></div>`
  if (region.starterProof) {
    html += `<h3>Lean starter (${esc(region.starterProof.trust)})</h3><pre>${esc(
      region.starterProof.text,
    )}</pre>`
  }
  return {name: region.label, sub: region.authoringState, html}
}

export function proofBoundaryDetail(map: any, id: string): Detail | null {
  const boundary = map.boundaries.find((row: any) => row.id === id)
  if (!boundary) return null
  const node = map.refinementGraph.nodes.find((row: any) => row.id === `contract-${id}`)
  const annotation = map.authoringRegions.find((row: any) => (row.boundaryIds || []).includes(id))
  return {
    name: boundary.qualified,
    sub: 'selected Level 1 instance',
    html: `<div class="kv"><span>source region</span><span>${esc(node.source)}</span>
    <span>entry</span><span>${hex(boundary.entryPc)}</span>
    <span>instructions</span><span>${boundary.ownedInstructionCount} owned; ${
      boundary.subtreeInstructionCount
    } execution closure</span>
    <span>observed vectors</span><span>${esc(boundary.observedVectors.join(', ') || 'none')}</span>
    <span>observed exits</span><span>${esc(
      boundary.observedExitTransitions
        .map((edge: any) => `${hex(edge[0])} → ${hex(edge[1])}`)
        .join(', ') || 'none',
    )}</span>
    <span>evidence</span><span>${esc(boundary.evidenceStatus)}</span>
    <span>contract</span><span>${esc(boundary.contractStatus.replaceAll('_', ' '))}</span>
    <span>machine proof</span><span>${esc(boundary.proofStatus.replaceAll('_', ' '))}</span>
    <span>authoring blocker</span><span>${esc(
      annotation?.blocker || 'no focused authoring annotation',
    )}</span></div>`,
  }
}

export function refinementNodeDetail(map: any, id: string): Detail | null {
  const node = map.refinementGraph.nodes.find((row: any) => row.id === id)
  if (!node) return null
  if (node.kind === 'level1Contract') return proofBoundaryDetail(map, node.boundaryId)
  if (node.kind === 'parentGlue') {
    const phase = map.phases.find((row: any) => row.id === node.phase)
    const phasePcs = new Set(phase.pcs)
    const pcs = map.instructions.filter((row: any) => phasePcs.has(row.pc))
    return {
      name: node.label,
      sub: node.kind,
      html: `<div class="kv"><span>obligation</span><span>prove parent-owned machine instructions while consuming selected child contracts</span>
      <span>proof status</span><span>${esc(node.proofStatus.replaceAll('_', ' '))}</span>
      <span>progress</span><span>${node.provedInstructionCount}/${
        node.instructionCount
      } instructions kernel-linked</span>
      <span>inline attribution</span><span>${
        node.absorbedInlineInstructionCount
      } DWARF-unclaimed instructions reviewed into inline Level 1 contracts</span>
      <span>phase</span><span>${esc(phase.label)}</span></div><pre>${pcs
        .map((row: any) => `${hex(row.pc)}  ${row.mnemonic.padEnd(7)} ${row.operands}`)
        .join('\n')}</pre>`,
    }
  }
  const text =
    node.kind === 'conversion'
      ? 'This theorem must consume every Level1ContractAssumptions field and prove main-owned instructions to derive ExportedContractAssumptions.'
      : 'This is the single public compliance theorem, currently conditional on Level1ContractAssumptions.'
  return {
    name: node.label,
    sub: node.kind,
    html: `<div class="kv"><span>status</span><span>${esc(
      node.status,
    )}</span><span>role</span><span>${esc(text)}</span></div>`,
  }
}

export function ZesuProofMapView() {
  const theme = useTheme()
  const [map, setMap] = useState<any>(null)
  const [error, setError] = useState<string | null>(null)
  const [filter, setFilter] = useState('all')
  const [detail, setDetail] = useState<Detail | null>(null)
  const leftRef = useRef<HTMLDivElement | null>(null)

  useEffect(() => {
    let live = true
    fetch(PROOF_MAP_URL)
      .then(response => response.json())
      .then(loaded => live && setMap(loaded))
      .catch(() => live && setError(`Could not load ${PROOF_MAP_URL}.`))
    return () => {
      live = false
    }
  }, [])

  const onClick = useCallback(
    (event: MouseEvent) => {
      if (!map) return
      const target = event.target as HTMLElement | null
      const filterButton = target?.closest('[data-filter]') as HTMLElement | null
      if (filterButton) {
        setFilter(filterButton.dataset.filter!)
        return
      }
      const card = target?.closest('[data-region]') as HTMLElement | null
      if (card) {
        setDetail(authoringRegionDetail(map, card.dataset.region!))
        return
      }
      const graphNode = target?.closest('[data-graph-id]') as HTMLElement | null
      if (graphNode) {
        setDetail(refinementNodeDetail(map, graphNode.dataset.graphId!))
      }
    },
    [map],
  )

  const body = error
    ? `<div class="muted">${esc(error)}</div>`
    : map
      ? renderProofMap(map, filter)
      : '<div class="muted">Loading the proof map …</div>'

  return (
    <div
      className="zesu-proof-map"
      style={{background: theme.bgPrimaryColor, color: theme.fgPrimaryColor}}
    >
      <style dangerouslySetInnerHTML={{__html: proofMapCss(theme.bgSecondaryColor)}} />
      <div
        className="zesu-proof-left"
        ref={leftRef}
        onClick={onClick}
        dangerouslySetInnerHTML={{__html: body}}
      />
      <div className="zesu-proof-right">
        <div className="zesu-proof-head">
          <b>{detail?.name ?? '—'}</b> <span className="muted">{detail?.sub ?? ''}</span>
        </div>
        <div
          className="zesu-proof-body"
          dangerouslySetInnerHTML={{
            __html: detail?.html ?? '<div class="muted">Click a card or a graph node.</div>',
          }}
        />
      </div>
    </div>
  )
}

// The D3 viewer's stylesheet for these panels, kept verbatim so the panels read
// the same. Only the outer two-pane frame is new.
const proofMapCss = (panel: string) => `
.zesu-proof-map{position:absolute;inset:0;display:grid;
  grid-template-columns:minmax(0,1fr) minmax(360px,540px);overflow:hidden;
  font:13px/1.45 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}
.zesu-proof-left{overflow:auto;padding:14px;min-width:0}
.zesu-proof-right{display:flex;flex-direction:column;min-width:0;overflow:hidden;
  background:${panel};border-left:1px solid #262c36}
.zesu-proof-head{padding:10px 14px;border-bottom:1px solid #262c36}
.zesu-proof-body{flex:1;min-height:0;overflow:auto;padding:10px 14px}
.zesu-proof-map .muted{color:#8a93a3}
.zesu-proof-map button{background:#1e242e;color:inherit;border:1px solid #262c36;border-radius:5px;
  padding:4px 9px;font:inherit;cursor:pointer}
.zesu-proof-map button:hover{background:#252c38}
.zesu-proof-map button:disabled{opacity:.5;cursor:default}
.proof-summary{display:grid;grid-template-columns:repeat(3,minmax(150px,1fr));gap:10px;margin-bottom:14px}
.proof-stat,.author-card,.proof-block{background:#171c24;border:1px solid #262c36;border-radius:6px}
.proof-stat{padding:10px}.proof-stat b{font-size:20px;display:block}.proof-stat small{color:#8a93a3}
.meter{height:5px;background:#282e38;border-radius:5px;overflow:hidden;margin-top:8px}
.meter i{display:block;height:100%}
.proof-tools{display:flex;gap:8px;align-items:center;margin:8px 0 12px;flex-wrap:wrap}
.proof-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:8px}
.author-card{padding:9px;cursor:pointer;border-left:4px solid #e5b84b}
.author-card.proved{border-left-color:${coveredBorderColor}}
.author-card.blocked{border-left-color:#d95757}
.author-card:hover{background:#1d232d}
.author-card b{display:block}.author-card small{color:#8a93a3}
.cfg-canvas{min-width:980px;border:1px solid #262c36;border-radius:7px;background:#11151b;overflow:auto}
.cfg-canvas svg{display:block}
.cfg-column{fill:#141920;stroke:#252c35}
.cfg-column-title{fill:#aeb9ca;font-size:11px;font-weight:600}
.cfg-link{fill:none;stroke:#596579;stroke-width:1;opacity:.7}
.cfg-link.call{stroke:#b08ad8;stroke-dasharray:4 3}
.cfg-link.return{stroke:#68a4d4;stroke-dasharray:2 3}
.cfg-node-rect{stroke-width:1.2;rx:4;cursor:pointer}
.cfg-node-label{fill:#1e2520;font-size:9px;font-weight:650;pointer-events:none}
.cfg-node-sub{fill:#35423a;font-size:8px;pointer-events:none}
.trust-legend{display:flex;gap:12px;color:#8a93a3;font-size:11px;flex-wrap:wrap}
.trust-legend i{display:inline-block;width:10px;height:10px;border-radius:2px;margin-right:4px}
.zesu-proof-map .kv{display:grid;grid-template-columns:auto 1fr;gap:2px 10px;margin:8px 0 12px;font-size:12px}
.zesu-proof-map .kv span:nth-child(odd){color:#8a93a3}
.zesu-proof-map pre{margin:0;white-space:pre;font-size:12px;overflow:auto}
`
