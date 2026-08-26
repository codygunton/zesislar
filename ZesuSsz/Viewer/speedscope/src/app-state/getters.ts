import {Frame, Profile} from '../lib/profile'
import {memoizeByReference, memoizeByShallowEquality} from '../lib/utils'
import {RowAtlas} from '../gl/row-atlas'
import {CanvasContext} from '../gl/canvas-context'
import {FlamechartRowAtlasKey} from '../gl/flamechart-renderer'
import {Theme} from '../views/themes/theme'
import {BUCKET_SHADES, PROOF_STATUS_COUNT, bucketForStatus} from '../views/themes/proof-palette'

export const createGetColorBucketForFrame = memoizeByReference(
  (frameToColorBucket: Map<number | string, number>) => {
    return (frame: Frame): number => {
      return frameToColorBucket.get(frame.key) || 0
    }
  },
)

export const createGetCSSColorForFrame = memoizeByShallowEquality(
  ({
    theme,
    frameToColorBucket,
  }: {
    theme: Theme
    frameToColorBucket: Map<number | string, number>
  }) => {
    const getColorBucketForFrame = createGetColorBucketForFrame(frameToColorBucket)
    return (frame: Frame): string => {
      const t = getColorBucketForFrame(frame) / 255
      return theme.colorForBucket(t).toCSS()
    }
  },
)

export const getCanvasContext = memoizeByShallowEquality(
  ({theme, canvas}: {theme: Theme; canvas: HTMLCanvasElement}) => {
    return new CanvasContext(canvas, theme)
  },
)

export const getRowAtlas = memoizeByReference((canvasContext: CanvasContext) => {
  return new RowAtlas<FlamechartRowAtlasKey>(
    canvasContext.gl,
    canvasContext.rectangleBatchRenderer,
    canvasContext.textureRenderer,
  )
})

export const getProfileToView = memoizeByShallowEquality(
  ({profile, flattenRecursion}: {profile: Profile; flattenRecursion: boolean}): Profile => {
    return flattenRecursion ? profile.getProfileWithRecursionFlattened() : profile
  },
)
export const getFrameToColorBucket = memoizeByReference(
  (profile: Profile): Map<string | number, number> => {
    const frames: Frame[] = []
    profile.forEachFrame(f => frames.push(f))

    const frameToColorBucket = new Map<string | number, number>()
    // A zesu profile carries the resolved proof status of every frame in `col`.
    // Colour by that status; fall back to the upstream name gradient when the
    // profile comes from anywhere else.
    const hasProofStatus = frames.some(f => f.col !== undefined && f.col !== null)
    if (hasProofStatus) {
      // Every frame in one status would otherwise get an identical color, and a
      // run of neighbouring frames then reads as one solid block. Add a stable
      // per-frame offset inside the status band so the theme can shade each
      // frame differently while keeping the status meaning.
      function shadeOffset(f: Frame): number {
        const name = (f.file || '') + f.name
        let hash = 0
        for (let i = 0; i < name.length; i++) {
          hash = (hash * 31 + name.charCodeAt(i)) | 0
        }
        return Math.abs(hash) % BUCKET_SHADES
      }
      for (const f of frames) {
        const status = Math.min(PROOF_STATUS_COUNT - 1, Math.max(0, f.col ?? 0))
        frameToColorBucket.set(f.key, bucketForStatus(status, shadeOffset(f)))
      }
    } else {
      function key(f: Frame) {
        return (f.file || '') + f.name
      }
      function compare(a: Frame, b: Frame) {
        return key(a) > key(b) ? 1 : -1
      }
      frames.sort(compare)
      for (let i = 0; i < frames.length; i++) {
        frameToColorBucket.set(frames[i].key, Math.floor((255 * i) / frames.length))
      }
    }

    return frameToColorBucket
  },
)
