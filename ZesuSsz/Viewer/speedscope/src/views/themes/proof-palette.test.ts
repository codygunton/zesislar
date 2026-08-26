import {
  BUCKET_BAND,
  BUCKET_SHADES,
  COVERED_BY_PROVED_PARENT,
  PROOF_STATUS_COUNT,
  bucketForStatus,
  colorForBucket,
  colorForBucketGLSL,
} from './proof-palette'

// The status a bucket decodes to, the way the shader decodes it.
const statusForBucket = (bucket: number) => Math.floor(((bucket / 255) * 255) / BUCKET_BAND)

describe('proof bucket layout', () => {
  it('keeps every status inside its own band', () => {
    for (let status = 0; status < PROOF_STATUS_COUNT; status++) {
      for (let shade = 0; shade < BUCKET_SHADES; shade++) {
        expect(statusForBucket(bucketForStatus(status, shade))).toBe(status)
      }
    }
  })

  it('survives the one-bucket error the 8-bit texture can add', () => {
    // A bucket travels through an 8-bit channel that can shift it by one, so a
    // status must still decode correctly at both neighbours of every shade.
    for (let status = 0; status < PROOF_STATUS_COUNT; status++) {
      for (let shade = 0; shade < BUCKET_SHADES; shade++) {
        const bucket = bucketForStatus(status, shade)
        expect(statusForBucket(bucket - 1)).toBe(status)
        expect(statusForBucket(bucket + 1)).toBe(status)
      }
    }
  })

  it('stays inside one byte', () => {
    expect(bucketForStatus(PROOF_STATUS_COUNT - 1, BUCKET_SHADES - 1)).toBeLessThan(255)
  })
})

describe('proof palette', () => {
  const cssFor = (status: number, shade = 0) =>
    colorForBucket(bucketForStatus(status, shade) / 255).toCSS()

  it('paints each proof state its documented color', () => {
    // 0 no progress, 2 proof in progress, 4 proven unconditionally: solid.
    expect(cssFor(0)).toBe('rgba(243, 170, 170, 1.00)')
    expect(cssFor(2)).toBe('rgba(255, 227, 154, 1.00)')
    expect(cssFor(4)).toBe('rgba(168, 230, 184, 1.00)')
    // 5 covered by a proved parent: white, and it takes no shade.
    expect(cssFor(COVERED_BY_PROVED_PARENT)).toBe('rgba(255, 255, 255, 1.00)')
    expect(cssFor(COVERED_BY_PROVED_PARENT, BUCKET_SHADES - 1)).toBe('rgba(255, 255, 255, 1.00)')
  })

  it('blends the two stripe colors where a stripe cannot be drawn', () => {
    // 1 contract specified is yellow over red; 3 proven conditionally is green
    // over yellow. A colour chit is one flat colour, so it shows the blend, and
    // that blend must sit between the two stripes.
    const between = (status: number, lo: string, hi: string, channel: 'r' | 'g' | 'b') => {
      const value = colorForBucket(bucketForStatus(status, 0) / 255)[channel]
      const a = parseInt(lo, 16) / 255
      const b = parseInt(hi, 16) / 255
      expect(value).toBeGreaterThan(Math.min(a, b) - 0.001)
      expect(value).toBeLessThan(Math.max(a, b) + 0.001)
    }
    between(1, 'f3', 'ff', 'r')
    between(1, 'aa', 'e3', 'g')
    between(3, 'a8', 'ff', 'r')
    between(3, 'b8', '9a', 'b')
    expect(cssFor(1)).not.toBe(cssFor(2))
    expect(cssFor(3)).not.toBe(cssFor(4))
  })

  it('shades frames of one status apart without changing the status', () => {
    const first = cssFor(0, 0)
    const last = cssFor(0, BUCKET_SHADES - 1)
    expect(first).not.toBe(last)
    expect(statusForBucket(bucketForStatus(0, BUCKET_SHADES - 1))).toBe(0)
  })
})

describe('proof palette shader', () => {
  it('declares the entry points the color pass calls', () => {
    expect(colorForBucketGLSL).toContain('vec3 colorForBucket(float t)')
    expect(colorForBucketGLSL).toContain('vec4 edgeColorForBucket(float t)')
  })

  it('uses the stripe period the color pass supplies', () => {
    expect(colorForBucketGLSL).toContain('stripePeriod')
    expect(colorForBucketGLSL).toContain('gl_FragCoord')
  })

  it('gives the covered state a green border and every other state none', () => {
    expect(colorForBucketGLSL).toContain('vec4(0.0, 0.0, 0.0, 0.0)')
    expect(colorForBucketGLSL).toContain('vec3(0.4039, 0.7176, 0.4902)')
  })
})
