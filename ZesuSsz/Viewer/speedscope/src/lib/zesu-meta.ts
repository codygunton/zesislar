// Metadata the zesu binary-regions profile carries beside the flamechart.
//
// The profile embeds one compact record per displayed function instance, which
// is what the header line, the level rail, and the color pass need. The full
// record for an instance — call edges, carrier routes, source text — stays in a
// separate details payload that this module fetches once, on the first click,
// the way the D3 viewer fetched it.

export interface ZesuFrameMeta {
  name?: string
  owner?: string
  machineOwner?: string
  qualified?: string
  displayTreeLevel?: number
  refinementLevel?: number
  machineInstructionCount?: number
  status: string
  theorem?: string
  contract?: string
  condition?: string
  coveringTheorem?: string
  selfInstructions?: number
  totalInstructions?: number
}

export interface ZesuProfileInfo {
  scope: 'decode' | 'full'
  total: number
  programTotal: number
  detailsUrl: string
}

const PROOF_STATUS_LABELS: string[] = [
  'no progress',
  'contract specified',
  'proof in progress',
  'proven conditionally on contracts',
  'proven unconditionally',
  'covered by a proved parent; no direct proof',
]

let frameMeta: ZesuFrameMeta[] = []
// The first instance of a machine symbol names it; call edges reference symbols
// by that machine owner, so the detail panel resolves them through this index.
let machineOwnerNames: Map<string, string> = new Map()
let profileInfo: ZesuProfileInfo | null = null
let detailsPromise: Promise<any[]> | null = null

export function setZesuMeta(meta: ZesuFrameMeta[], info: ZesuProfileInfo | null): void {
  frameMeta = meta
  profileInfo = info
  detailsPromise = null
  machineOwnerNames = new Map()
  for (const row of meta) {
    if (row.machineOwner && !machineOwnerNames.has(row.machineOwner)) {
      machineOwnerNames.set(row.machineOwner, row.qualified ?? row.machineOwner)
    }
  }
}

export function qualifiedForMachineOwner(owner: string): string {
  return machineOwnerNames.get(owner) ?? owner
}

export function getZesuMeta(uiId: string | null | undefined): ZesuFrameMeta | null {
  if (uiId == null) return null
  const index = parseInt(uiId, 10)
  if (!isFinite(index)) return null
  return frameMeta[index] ?? null
}

export function hasZesuMeta(): boolean {
  return frameMeta.length > 0
}

export function getZesuProfileInfo(): ZesuProfileInfo | null {
  return profileInfo
}

export function proofStatusLabel(col: number | undefined | null): string {
  return PROOF_STATUS_LABELS[col ?? 0] ?? 'unknown'
}

// The details payload is a plain array indexed by the same uiId as the frames.
export async function getZesuDetails(uiId: string | null | undefined): Promise<any | null> {
  if (uiId == null || !profileInfo) return null
  if (!detailsPromise) {
    detailsPromise = fetch(profileInfo.detailsUrl).then(response => response.json())
  }
  const details = await detailsPromise
  const index = parseInt(uiId, 10)
  return details[index] ?? null
}
