import {Atom} from './atom'

// The bottom detail panel is an overlay over the flamechart: it floats above the
// chart rather than taking space from it, so the chart's own geometry never
// depends on it. The viewer drags its top edge to resize, drags it to the bottom
// or presses its button to collapse, and drags up or presses the button again to
// reopen.

export const MIN_DETAIL_VIEW_HEIGHT = 90
export const COLLAPSED_DETAIL_VIEW_HEIGHT = 24

// Dragging below this closes the panel, so the drag can dismiss it outright.
const CLOSE_BELOW_HEIGHT = 60

export interface DetailViewLayout {
  // Height when open, remembered while collapsed so reopening restores it.
  height: number
  open: boolean
}

export const detailViewLayoutAtom = new Atom<DetailViewLayout>(
  {height: 150, open: true},
  'zesuDetailViewLayout',
)

function maxHeight(): number {
  return Math.max(MIN_DETAIL_VIEW_HEIGHT, window.innerHeight - 120)
}

// Height the panel occupies right now, collapsed or not.
export function currentDetailViewHeight(layout: DetailViewLayout): number {
  return layout.open ? layout.height : COLLAPSED_DETAIL_VIEW_HEIGHT
}

// Called while dragging the top edge. A drag that reaches the bottom collapses.
export function dragDetailViewTo(height: number): void {
  const layout = detailViewLayoutAtom.get()
  if (height < CLOSE_BELOW_HEIGHT) {
    if (layout.open) detailViewLayoutAtom.set({...layout, open: false})
    return
  }
  const next = Math.round(Math.min(maxHeight(), Math.max(MIN_DETAIL_VIEW_HEIGHT, height)))
  if (layout.open && next === layout.height) return
  detailViewLayoutAtom.set({height: next, open: true})
}

export function toggleDetailView(): void {
  const layout = detailViewLayoutAtom.get()
  detailViewLayoutAtom.set({...layout, open: !layout.open})
}
