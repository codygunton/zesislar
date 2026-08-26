import {StyleDeclarationValue, StyleSheet, css} from 'aphrodite'
import {h, JSX} from 'preact'
import {getFlamechartStyle} from './flamechart-style'
import {formatPercent} from '../lib/utils'
import {Frame, CallTreeNode} from '../lib/profile'
import {ColorChit} from './color-chit'
import {Flamechart} from '../lib/flamechart'
import {useTheme} from './themes/theme'
import {useEffect, useState} from 'preact/hooks'
import {clearLevelSelection, levelSelectionAtom} from '../lib/zesu-level'
import {useAtom} from '../lib/atom'
import {
  currentDetailViewHeight,
  detailViewLayoutAtom,
  dragDetailViewTo,
  toggleDetailView,
} from '../lib/zesu-detail-height'
import {
  getZesuDetails,
  getZesuMeta,
  hasZesuMeta,
  proofStatusLabel,
  qualifiedForMachineOwner,
} from '../lib/zesu-meta'

interface StatisticsTableProps {
  title: string
  grandTotal: number
  selectedTotal: number
  selectedSelf: number
  cellStyle: StyleDeclarationValue
  formatter: (v: number) => string
}

function StatisticsTable(props: StatisticsTableProps) {
  const style = getFlamechartStyle(useTheme())

  const total = props.formatter(props.selectedTotal)
  const self = props.formatter(props.selectedSelf)
  const totalPerc = (100.0 * props.selectedTotal) / props.grandTotal
  const selfPerc = (100.0 * props.selectedSelf) / props.grandTotal

  return (
    <div className={css(style.statsTable)}>
      <div className={css(props.cellStyle, style.statsTableCell, style.statsTableHeader)}>
        {props.title}
      </div>

      <div className={css(props.cellStyle, style.statsTableCell)}>Total</div>
      <div className={css(props.cellStyle, style.statsTableCell)}>Self</div>

      <div className={css(props.cellStyle, style.statsTableCell)}>{total}</div>
      <div className={css(props.cellStyle, style.statsTableCell)}>{self}</div>

      <div className={css(props.cellStyle, style.statsTableCell)}>
        {formatPercent(totalPerc)}
        <div className={css(style.barDisplay)} style={{height: `${totalPerc}%`}} />
      </div>
      <div className={css(props.cellStyle, style.statsTableCell)}>
        {formatPercent(selfPerc)}
        <div className={css(style.barDisplay)} style={{height: `${selfPerc}%`}} />
      </div>
    </div>
  )
}

interface StackTraceViewProps {
  getFrameColor: (frame: Frame) => string
  node: CallTreeNode
}
function StackTraceView(props: StackTraceViewProps) {
  const style = getFlamechartStyle(useTheme())

  const rows: JSX.Element[] = []
  let node: CallTreeNode | null = props.node
  for (; node && !node.isRoot(); node = node.parent) {
    const row: (JSX.Element | string)[] = []
    const {frame} = node

    row.push(<ColorChit color={props.getFrameColor(frame)} />)

    if (rows.length) {
      row.push(<span className={css(style.stackFileLine)}>&gt; </span>)
    }
    row.push(frame.name)

    if (frame.file && !hasZesuMeta()) {
      let pos = frame.file
      if (frame.line != null) {
        pos += `:${frame.line}`
        if (frame.col != null) {
          pos += `:${frame.col}`
        }
      }
      row.push(<span className={css(style.stackFileLine)}> ({pos})</span>)
    }
    rows.push(<div className={css(style.stackLine)}>{row}</div>)
  }
  return (
    <div className={css(style.stackTraceView)}>
      <div className={css(style.stackTraceViewPadding)}>{rows}</div>
    </div>
  )
}

interface FlamechartDetailViewProps {
  flamechart: Flamechart
  getCSSColorForFrame: (frame: Frame) => string
  selectedNode: CallTreeNode
}

const metaStyles = StyleSheet.create({
  metaPanel: {
    padding: '4px 8px',
    fontSize: 12,
    lineHeight: '18px',
    overflow: 'auto',
    height: '100%',
  },
  metaRow: {
    display: 'flex',
    gap: 8,
  },
  metaLabel: {
    fontWeight: 'bold',
    minWidth: 190,
    flexShrink: 0,
  },
  metaValue: {
    wordBreak: 'break-word' as const,
    whiteSpace: 'pre-wrap' as const,
  },
  metaTitle: {
    fontWeight: 'bold',
    marginBottom: 4,
    wordBreak: 'break-all' as const,
  },
  metaLevel: {
    fontWeight: 'normal',
    opacity: 0.7,
  },
  metaSource: {
    marginTop: 6,
    overflowX: 'auto' as const,
    whiteSpace: 'pre' as const,
  },
  levelView: {
    gridColumn: '1 / -1',
  },
  collapsedBar: {
    gridColumn: '1 / -1',
    display: 'flex',
    alignItems: 'center',
    padding: '0 10px',
    fontSize: 11,
    cursor: 'pointer',
    whiteSpace: 'nowrap',
    overflow: 'hidden',
    textOverflow: 'ellipsis',
  },
  levelButton: {
    marginLeft: 8,
    font: 'inherit',
    cursor: 'pointer',
  },
})

// A grab bar along the top edge of the detail panel. Dragging it up gives the
// panel more room and dragging it down gives the flamechart more.
// The panel's top edge. Dragging it resizes the panel; dragging it to the bottom
// of the window collapses it, and dragging up from collapsed reopens it.
export function DetailViewResizeHandle() {
  const style = getFlamechartStyle(useTheme())

  const onMouseDown = (start: MouseEvent) => {
    start.preventDefault()
    const onMove = (move: MouseEvent) => dragDetailViewTo(window.innerHeight - move.clientY)
    const onUp = () => {
      window.removeEventListener('mousemove', onMove)
      window.removeEventListener('mouseup', onUp)
      document.body.style.cursor = ''
    }
    document.body.style.cursor = 'ns-resize'
    window.addEventListener('mousemove', onMove)
    window.addEventListener('mouseup', onUp)
  }

  return <div className={css(style.detailViewResizeHandle)} onMouseDown={onMouseDown} />
}

// Collapse/expand control. The caret points the way the panel will move.
function DetailViewToggle({open}: {open: boolean}) {
  const style = getFlamechartStyle(useTheme())
  return (
    <div
      className={css(style.detailViewToggle)}
      onMouseDown={(ev: MouseEvent) => ev.stopPropagation()}
      onClick={toggleDetailView}
      title={open ? 'Collapse the detail panel' : 'Open the detail panel'}
    >
      {open ? '▾' : '▴'}
    </div>
  )
}

// The panel frame: the resize handle, the collapse control, and the panel body
// when it is open.
export function DetailViewFrame({title, children}: {title: string; children?: any}) {
  const style = getFlamechartStyle(useTheme())
  const layout = useAtom(detailViewLayoutAtom)
  const height = currentDetailViewHeight(layout)

  return (
    <div className={css(style.detailView)} style={{height}}>
      <DetailViewResizeHandle />
      <DetailViewToggle open={layout.open} />
      {layout.open ? (
        children
      ) : (
        <div className={css(metaStyles.collapsedBar)} onClick={toggleDetailView}>
          {title}
        </div>
      )}
    </div>
  )
}

const hex = (value: number | null | undefined): string =>
  value == null ? '?' : `0x${value.toString(16)}`

const list = (rows: string[]): string => (rows.length ? rows.join('\n') : 'none')

// The active callee tree is a nested record; the D3 viewer printed it as an
// indented line per frame, and reading it that way is why it is here.
function frameTree(frames: any[], depth: number): string[] {
  const rows: string[] = []
  for (const frame of frames ?? []) {
    const target = frame.targetIdentity?.qualified ?? '?'
    const source = frame.sourcePc == null ? 'source-derived sites' : hex(frame.sourcePc)
    const returns = (frame.returnSites ?? [])
      .map((site: any) => `${hex(site.sourcePc)}→${hex(site.returnPc)}`)
      .join(', ')
    const transitions = frame.cycleBackEdge?.transitions ?? []
    const cycle = frame.cycleBackEdge
      ? `; back-edge to ${frame.cycleBackEdge.ancestorIdentity?.qualified ?? '?'} (${
          transitions.length
        } transition${transitions.length === 1 ? '' : 's'})`
      : ''
    rows.push(
      `${'· '.repeat(depth)}${frame.kind} ${source} → ${target} @ ${hex(frame.targetPc)} (${
        (frame.activeCalleeExecutionPcs ?? []).length
      } PCs${returns ? `; RA ${returns}` : ''}${cycle})`,
    )
    rows.push(...frameTree(frame.activeCalleeFrames ?? [], depth + 1))
  }
  return rows
}

function detailRows(meta: any, detail: any, node: CallTreeNode): [string, string][] {
  const path: string[] = []
  for (let n: CallTreeNode | null = node; n && !n.isRoot(); n = n.parent) {
    path.unshift(n.frame.name)
  }
  const d = detail ?? {}
  const calls = (d.callees ?? []).map(
    (call: any) => `${call.kind} → ${qualifiedForMachineOwner(call.callee)}`,
  )
  const callers = (d.callers ?? []).map(
    (call: any) =>
      `${call.kind} ← ${
        call.caller === 'program' ? 'program' : qualifiedForMachineOwner(call.caller)
      }`,
  )
  const tails = (d.tailDependencies ?? []).map(
    (tail: any) =>
      `${tail.qualified}: ${hex(tail.transfer.source)} → ${hex(
        tail.transfer.target,
      )}, completes at ${(tail.completionSourcePcs ?? []).map(hex).join(', ')}`,
  )
  const handoffs = (d.fragmentHandoffs ?? []).map(
    (edge: any) => `${hex(edge.sourcePc)} → ${hex(edge.targetPc)}`,
  )
  const reentries = (d.parentReentryEdges ?? []).map(
    (edge: any) => `${hex(edge.sourcePc)} → ${hex(edge.targetPc)}`,
  )
  const carrierRoutes = (d.carrierRoutes ?? []).map((route: any) => {
    const handoff = route.handoff ?? {}
    const carriers = (route.carrierPcs ?? []).map(hex).join(', ') || 'none'
    const paths =
      (route.carrierPaths ?? [])
        .map((carrierPath: any) => carrierPath.pcs.map(hex).join(' → '))
        .join('; ') || 'none'
    const claim =
      route.classification === 'sourceReviewedOutcomePath' ? 'unmeasured' : 'not claimed'
    return `${route.classification ?? 'unclassified'}: ${hex(handoff.sourcePc)} → ${hex(
      handoff.targetPc,
    )}; carriers ${carriers}; paths ${paths}; registers/stack/status/allocation/HeapArrayRep ${claim}`
  })
  const displayCallsites = (d.displayCallsites ?? []).map(hex).join(', ')

  return [
    ['stack path', path.join(' › ')],
    ['instance kind', d.kind ?? '?'],
    [
      'callsite / return',
      d.callsitePc == null ? 'program entry' : `${hex(d.callsitePc)} / ${hex(d.returnPc)}`,
    ],
    ['proof status', proofStatusLabel(node.frame.col)],
    ['contract/theorem', meta?.theorem ?? meta?.contract ?? 'none'],
    ['covering parent theorem', meta?.coveringTheorem ?? 'none'],
    ['outstanding condition', meta?.condition ?? 'none'],
    [
      'hierarchy parent',
      `${d.displayAnchorName ?? 'lexical DWARF parent'}${
        displayCallsites ? ` at ${displayCallsites}` : ''
      }`,
    ],
    ['machine-symbol callers', list(callers)],
    ['actual calls', list(calls)],
    ['resolved tail route', list(tails)],
    ['attribution subtree handoffs', handoffs.join(', ') || 'none'],
    ['parent subtree reentries', reentries.join(', ') || 'none'],
    ['carrier routes', list(carrierRoutes)],
    ['active callee tree', list(frameTree(d.activeCalleeFrames ?? [], 0))],
    ['source', `${d.file ?? '?'}:${d.line ?? '?'}`],
    ['instance instructions', String(meta?.machineInstructionCount ?? node.getSelfWeight())],
    ['subtree instructions', String(node.getTotalWeight())],
    ['fragments', d.frags > 1 ? `${d.frags} (non-contiguous)` : '1 (contiguous)'],
    [
      'tree placement',
      `${d.displayRelation ?? 'actual call-tree placement'}${
        d.cycleTruncated ? ' — recursive expansion stops here' : ''
      }`,
    ],
    ['entries', (d.entries ?? []).map(hex).join(', ') || 'none'],
    ['exits', String((d.exits ?? []).length)],
    ['loop SCCs', (d.loopSccs ?? []).join(', ') || 'none'],
  ]
}

function ZesuMetaView({node}: {node: CallTreeNode}) {
  const uiId = node.frame.file ?? ''
  const meta = getZesuMeta(uiId)
  const [detail, setDetail] = useState<any>(null)

  useEffect(() => {
    let live = true
    setDetail(null)
    getZesuDetails(uiId).then(loaded => {
      if (live) setDetail(loaded)
    })
    return () => {
      live = false
    }
  }, [uiId])

  return (
    <div className={css(metaStyles.metaPanel)}>
      <div className={css(metaStyles.metaTitle)}>
        {meta?.qualified ?? node.frame.name}
        <span className={css(metaStyles.metaLevel)}>
          {' '}
          Level {meta?.refinementLevel ?? meta?.displayTreeLevel ?? '?'}
        </span>
      </div>
      {detailRows(meta, detail, node).map(([label, value]) => (
        <div className={css(metaStyles.metaRow)}>
          <span className={css(metaStyles.metaLabel)}>{label}</span>
          <span className={css(metaStyles.metaValue)}>{value}</span>
        </div>
      ))}
      {detail?.src && <pre className={css(metaStyles.metaSource)}>{detail.src.text}</pre>}
    </div>
  )
}

// The rail label a viewer clicked, and every function instance the flamechart
// displays at that level. The D3 viewer reported both in its side panel.
export function ZesuLevelDetailView() {
  const selection = useAtom(levelSelectionAtom)
  if (!selection) return null

  return (
    <DetailViewFrame title={`Level ${selection.level}`}>
      <div className={css(metaStyles.metaPanel, metaStyles.levelView)}>
        <div className={css(metaStyles.metaTitle)}>
          Level {selection.level}
          <span className={css(metaStyles.metaLevel)}>
            {' '}
            {selection.names.length} displayed function instances
          </span>
          <button className={css(metaStyles.levelButton)} onClick={clearLevelSelection}>
            close
          </button>
        </div>
        {selection.names.length ? (
          <pre className={css(metaStyles.metaSource)}>{selection.names.join('\n')}</pre>
        ) : (
          <div>No named functions at this level.</div>
        )}
      </div>
    </DetailViewFrame>
  )
}

export function FlamechartDetailView(props: FlamechartDetailViewProps) {
  const style = getFlamechartStyle(useTheme())

  const {flamechart, selectedNode} = props
  const {frame} = selectedNode

  return (
    <DetailViewFrame title={getZesuMeta(frame.file)?.qualified ?? frame.name}>
      <StatisticsTable
        title={'This Instance'}
        cellStyle={style.thisInstanceCell}
        grandTotal={flamechart.getTotalWeight()}
        selectedTotal={selectedNode.getTotalWeight()}
        selectedSelf={selectedNode.getSelfWeight()}
        formatter={flamechart.formatValue.bind(flamechart)}
      />
      <StatisticsTable
        title={'All Instances'}
        cellStyle={style.allInstancesCell}
        grandTotal={flamechart.getTotalWeight()}
        selectedTotal={frame.getTotalWeight()}
        selectedSelf={frame.getSelfWeight()}
        formatter={flamechart.formatValue.bind(flamechart)}
      />
      {hasZesuMeta() && <ZesuMetaView node={selectedNode} />}
      <StackTraceView node={selectedNode} getFrameColor={props.getCSSColorForFrame} />
    </DetailViewFrame>
  )
}
