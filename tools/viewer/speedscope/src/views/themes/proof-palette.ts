import {Color} from '../../lib/color'

// The zesu proof palette. Both this view and the binary-regions README state the
// same six meanings, so the colors must stay identical:
//
//   0 no progress                     red
//   1 contract specified              yellow and red stripes
//   2 proof in progress               yellow
//   3 proven conditionally            green and yellow stripes
//   4 proven unconditionally          green
//   5 covered by a proved parent      white with a green border
//
// A frame's color bucket carries its status in the high part and a stable shade
// offset in the low part. Without the shade a run of frames in one status reads
// as a single solid block.

export const PROOF_STATUS_COUNT = 6

// Bucket layout. A bucket travels through an 8-bit texture channel, which can
// move it by one, so a status band reserves slot 0 and slot BAND-1 and never
// uses them. A one-bucket error then stays inside its own band.
export const BUCKET_BAND = 42
export const BUCKET_SHADES = 40

export const bucketForStatus = (status: number, shade: number): number =>
  status * BUCKET_BAND + 1 + (shade % BUCKET_SHADES)

// Pastel fill, darker companion, and the second stripe color. A status with no
// stripe repeats its fill.
const statusColors: [string, string, string][] = [
  ['#f3aaaa', '#c96f6f', '#f3aaaa'], // no progress
  ['#ffe39a', '#d0b253', '#f3aaaa'], // contract specified: yellow over red
  ['#ffe39a', '#d0b253', '#ffe39a'], // proof in progress
  ['#a8e6b8', '#67b77d', '#ffe39a'], // proven conditionally: green over yellow
  ['#a8e6b8', '#67b77d', '#a8e6b8'], // proven unconditionally
  ['#ffffff', '#ffffff', '#ffffff'], // covered by a proved parent
]

// How far a frame may shade from the pastel fill toward its darker companion.
// Kept below 1 so the dark ink labels stay readable on every shade.
const SHADE_DEPTH = 0.55

// A frame covered by a proved parent is white; its green border carries the
// meaning, so it takes no shade.
export const COVERED_BY_PROVED_PARENT = 5
export const coveredBorderColor = '#67b77d'

// Dark ink for labels drawn on top of the pastel bars, in either theme.
export const frameLabelInk = '#1e2520'
export const frameLabelFadedInk = '#3f4b43'

const statusForBucket = (bucket: number): number =>
  Math.min(PROOF_STATUS_COUNT - 1, Math.max(0, Math.floor(bucket / BUCKET_BAND)))

const mixHex = (from: string, to: string, amount: number): Color => {
  const a = Color.fromCSSHex(from)
  const b = Color.fromCSSHex(to)
  return new Color(
    a.r + (b.r - a.r) * amount,
    a.g + (b.g - a.g) * amount,
    a.b + (b.b - a.b) * amount,
    1,
  )
}

// The CSS form paints color chits and table rows, which are too small to carry a
// stripe, so a striped status shows the blend of its two stripe colors.
export const colorForBucket = (t: number): Color => {
  const bucket = t * 255
  const status = statusForBucket(bucket)
  const shade = Math.min(1, Math.max(0, (bucket - status * BUCKET_BAND - 1) / (BUCKET_SHADES - 1)))
  const [fill, companion, stripe] = statusColors[status]
  if (status === COVERED_BY_PROVED_PARENT) return Color.fromCSSHex(fill)
  const shaded = mixHex(fill, companion, SHADE_DEPTH * shade)
  if (stripe === fill) return shaded
  const other = mixHex(stripe, companion, SHADE_DEPTH * shade)
  return new Color((shaded.r + other.r) / 2, (shaded.g + other.g) / 2, (shaded.b + other.b) / 2, 1)
}

const glslVec3 = (hex: string): string => {
  const color = Color.fromCSSHex(hex)
  return `vec3(${color.r.toFixed(4)}, ${color.g.toFixed(4)}, ${color.b.toFixed(4)})`
}

const glslBranches = (index: 0 | 1 | 2): string =>
  statusColors
    .slice(0, PROOF_STATUS_COUNT - 1)
    .map((row, status) => `    if (status < ${status}.5) return ${glslVec3(row[index])};`)
    .join('\n') + `\n    return ${glslVec3(statusColors[PROOF_STATUS_COUNT - 1][index])};`

// `stripePeriod` is supplied by the color pass; it is the stripe width in device
// pixels, so the stripes stay the same visual width on any display.
export const colorForBucketGLSL = `
  vec3 proofFill(float status) {
${glslBranches(0)}
  }
  vec3 proofCompanion(float status) {
${glslBranches(1)}
  }
  vec3 proofStripe(float status) {
${glslBranches(2)}
  }
  float proofStatusForBucket(float t) {
    return clamp(floor((t * 255.0) / ${BUCKET_BAND}.0), 0.0, ${PROOF_STATUS_COUNT - 1}.0);
  }
  vec3 colorForBucket(float t) {
    float bucket = t * 255.0;
    float status = proofStatusForBucket(t);
    float shade = clamp((bucket - status * ${BUCKET_BAND}.0 - 1.0) / ${
      BUCKET_SHADES - 1
    }.0, 0.0, 1.0);
    vec3 companion = proofCompanion(status);
    vec3 fill = mix(proofFill(status), companion, ${SHADE_DEPTH} * shade);
    vec3 stripe = mix(proofStripe(status), companion, ${SHADE_DEPTH} * shade);
    // A 45-degree stripe in screen space, so it reads the same at any zoom.
    float phase = fract((gl_FragCoord.x + gl_FragCoord.y) / (2.0 * stripePeriod));
    return phase < 0.5 ? fill : stripe;
  }
  // Frames covered by a proved parent are white, which needs a border to stay
  // separable from the page. Every other status draws its edge transparent, the
  // way upstream speedscope does.
  vec4 edgeColorForBucket(float t) {
    if (proofStatusForBucket(t) > ${COVERED_BY_PROVED_PARENT}.0 - 0.5) {
      return vec4(${glslVec3(coveredBorderColor)}, 1.0);
    }
    return vec4(0.0, 0.0, 0.0, 0.0);
  }
`
