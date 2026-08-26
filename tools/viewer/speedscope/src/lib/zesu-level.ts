import {Atom} from './atom'
import {Flamechart} from './flamechart'
import {getZesuMeta} from './zesu-meta'

// The refinement level a rail label names, and every function instance the
// flamechart displays at that level. The D3 viewer this replaced reported both
// when a rail label was clicked, so this view has to report them too.
export interface ZesuLevelSelection {
  level: number
  names: string[]
}

export const levelSelectionAtom = new Atom<ZesuLevelSelection | null>(null, 'zesuLevelSelection')

// A row's level is the level of the instances on it. Rows and levels are not the
// same thing: one level can occupy more than one row.
export function levelForDepth(flamechart: Flamechart, depth: number): number | null {
  const layer = flamechart.getLayers()[depth]
  if (!layer || layer.length === 0) return null
  // A profile from anywhere else carries no levels, so the row names none.
  const meta = getZesuMeta(layer[0].node.frame.file)
  if (!meta) return null
  return meta.displayTreeLevel ?? depth
}

export function selectLevel(flamechart: Flamechart, depth: number): void {
  const level = levelForDepth(flamechart, depth)
  if (level == null) return
  const names: string[] = []
  const seen = new Set<string>()
  flamechart.getLayers().forEach((layer, layerDepth) => {
    for (const frame of layer) {
      const meta = getZesuMeta(frame.node.frame.file)
      if ((meta?.displayTreeLevel ?? layerDepth) !== level) continue
      const name = meta?.qualified
      if (!name || seen.has(name)) continue
      seen.add(name)
      names.push(name)
    }
  })
  levelSelectionAtom.set({level, names})
}

export function clearLevelSelection(): void {
  if (levelSelectionAtom.get() !== null) levelSelectionAtom.set(null)
}
