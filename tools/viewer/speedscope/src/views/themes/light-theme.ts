import {Theme} from './theme'
import {
  colorForBucket,
  colorForBucketGLSL,
  frameLabelFadedInk,
  frameLabelInk,
} from './proof-palette'

// These colors are intentionally not exported from this file, because these
// colors are theme specific, and we want all color values to come from the
// active theme. The bars use the same zesu proof palette as the dark theme;
// only the chrome differs.
enum Colors {
  WHITE = '#FFFFFF',
  OFF_WHITE = '#F6F6F6',
  LIGHT_GRAY = '#BDBDBD',
  GRAY = '#5A6472',
  DARK_GRAY = '#222222',
  BLACK = '#111111',
  ACCENT = '#B8860B',
  ACCENT_DIM = '#F2C94C',
  GREEN = '#2F8F4E',
}

export const lightTheme: Theme = {
  fgPrimaryColor: Colors.BLACK,
  fgSecondaryColor: Colors.GRAY,

  bgPrimaryColor: Colors.WHITE,
  bgSecondaryColor: Colors.OFF_WHITE,

  altFgPrimaryColor: Colors.WHITE,
  altFgSecondaryColor: Colors.LIGHT_GRAY,

  altBgPrimaryColor: Colors.BLACK,
  altBgSecondaryColor: Colors.DARK_GRAY,

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
