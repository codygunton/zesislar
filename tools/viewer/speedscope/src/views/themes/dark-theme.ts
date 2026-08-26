import {Theme} from './theme'
import {
  colorForBucket,
  colorForBucketGLSL,
  frameLabelFadedInk,
  frameLabelInk,
} from './proof-palette'

// These colors are intentionally not exported from this file, because these
// colors are theme specific, and we want all color values to come from the
// active theme. The chrome colors match the zesu binary-regions UI.
enum Colors {
  BG = '#0F1115',
  PANEL = '#161A21',
  PANEL_ALT = '#1B2028',
  LINE = '#262C36',
  FG = '#DFE4EC',
  DIM = '#8A93A3',
  ACCENT = '#F2C94C',
  ACCENT_DIM = '#6B5726',
  GREEN = '#67B77D',
  BLACK = '#000000',
}

export const darkTheme: Theme = {
  fgPrimaryColor: Colors.FG,
  fgSecondaryColor: Colors.DIM,

  bgPrimaryColor: Colors.BG,
  bgSecondaryColor: Colors.PANEL,

  altFgPrimaryColor: Colors.FG,
  altFgSecondaryColor: Colors.DIM,

  altBgPrimaryColor: Colors.PANEL_ALT,
  altBgSecondaryColor: Colors.LINE,

  selectionPrimaryColor: Colors.ACCENT,
  selectionSecondaryColor: Colors.ACCENT_DIM,

  weightColor: Colors.GREEN,

  frameLabelPrimaryColor: frameLabelInk,
  frameLabelSecondaryColor: frameLabelFadedInk,

  searchMatchTextColor: Colors.BLACK,
  searchMatchPrimaryColor: Colors.ACCENT,
  searchMatchSecondaryColor: Colors.ACCENT_DIM,

  colorForBucket,
  colorForBucketGLSL,
}
