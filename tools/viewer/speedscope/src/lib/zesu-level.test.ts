import {Flamechart} from './flamechart'
import {setZesuMeta, ZesuFrameMeta} from './zesu-meta'
import {clearLevelSelection, levelForDepth, levelSelectionAtom, selectLevel} from './zesu-level'

// Rows and levels are not the same thing: `decode` and `encode` share a row but
// `inner` sits on its own row at the same level, and `leaf` has no name.
const META: ZesuFrameMeta[] = [
  {qualified: 'main', displayTreeLevel: 0, status: 'proved'},
  {qualified: 'decode', displayTreeLevel: 1, status: 'proved'},
  {qualified: 'encode', displayTreeLevel: 1, status: 'not_selected'},
  {qualified: 'inner', displayTreeLevel: 1, status: 'not_selected'},
  {qualified: 'decode', displayTreeLevel: 1, status: 'proved'},
  {qualified: 'deep', displayTreeLevel: 2, status: 'not_selected'},
]

// One layer per row, each holding the frames on that row.
const LAYERS = [[0], [1, 2], [3, 4], [5]]

function flamechart(): Flamechart {
  return {
    getLayers: () => LAYERS.map(row => row.map(id => ({node: {frame: {file: String(id)}}}))),
  } as unknown as Flamechart
}

describe('level rail selection', () => {
  beforeEach(() => {
    setZesuMeta(META, null)
    clearLevelSelection()
  })

  it('reads the level of a row from the instances on it', () => {
    expect(levelForDepth(flamechart(), 0)).toBe(0)
    expect(levelForDepth(flamechart(), 2)).toBe(1)
    expect(levelForDepth(flamechart(), 3)).toBe(2)
  })

  it('has no level for a row past the end', () => {
    expect(levelForDepth(flamechart(), 9)).toBeNull()
  })

  it('lists every instance at the level, across rows, without repeats', () => {
    selectLevel(flamechart(), 1)
    // Row 1 holds `decode` and `encode`; row 2 holds `inner` and a second
    // `decode`. All are Level 1, and the repeat is reported once.
    expect(levelSelectionAtom.get()).toEqual({level: 1, names: ['decode', 'encode', 'inner']})
  })

  it('selects the same level from any row that carries it', () => {
    selectLevel(flamechart(), 1)
    const fromFirstRow = levelSelectionAtom.get()
    clearLevelSelection()
    selectLevel(flamechart(), 2)
    expect(levelSelectionAtom.get()).toEqual(fromFirstRow)
  })

  it('reports the root level on its own', () => {
    selectLevel(flamechart(), 0)
    expect(levelSelectionAtom.get()).toEqual({level: 0, names: ['main']})
  })

  it('clears the selection', () => {
    selectLevel(flamechart(), 0)
    clearLevelSelection()
    expect(levelSelectionAtom.get()).toBeNull()
  })

  it('selects nothing when the profile carries no zesu metadata', () => {
    setZesuMeta([], null)
    selectLevel(flamechart(), 0)
    expect(levelSelectionAtom.get()).toBeNull()
  })
})
