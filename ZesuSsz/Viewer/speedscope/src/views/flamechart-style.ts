import {StyleSheet} from 'aphrodite'
import {FontSize, Sizes} from './style'
import {withTheme} from './themes/theme'

export const getFlamechartStyle = withTheme(theme =>
  StyleSheet.create({
    hoverCount: {
      color: theme.weightColor,
    },
    fill: {
      width: '100%',
      height: '100%',
      position: 'absolute',
      left: 0,
      top: 0,
    },
    minimap: {
      height: Sizes.MINIMAP_HEIGHT,
      borderBottom: `${Sizes.SEPARATOR_HEIGHT}px solid ${theme.fgSecondaryColor}`,
    },
    panZoomView: {
      flex: 1,
    },

    detailView: {
      display: 'grid',
      // The height is set inline: the panel is resizable.
      overflow: 'hidden',
      // The zesu metadata panel is a third pane, and it is long enough to need
      // its own scroll, so every pane gets a column that can shrink.
      gridTemplateColumns: '120px 120px minmax(0, 3fr) minmax(0, 2fr)',
      gridTemplateRows: '100%',
      borderTop: `${Sizes.SEPARATOR_HEIGHT}px solid ${theme.fgSecondaryColor}`,
      fontSize: FontSize.LABEL,
      position: 'absolute',
      background: theme.bgPrimaryColor,
      width: '100vw',
      bottom: 0,
    },
    stackTraceViewPadding: {
      padding: 5,
    },
    detailViewToggle: {
      position: 'absolute',
      top: 0,
      right: 0,
      width: 22,
      height: 18,
      lineHeight: '18px',
      textAlign: 'center',
      cursor: 'pointer',
      zIndex: 2,
      color: theme.fgSecondaryColor,
      ':hover': {
        color: theme.fgPrimaryColor,
        background: theme.altBgSecondaryColor,
      },
    },
    detailViewResizeHandle: {
      position: 'absolute',
      top: 0,
      left: 0,
      right: 0,
      height: 6,
      cursor: 'ns-resize',
      zIndex: 1,
      ':hover': {
        background: theme.selectionSecondaryColor,
      },
    },
    stackTraceView: {
      height: '100%',
      lineHeight: `${FontSize.LABEL + 2}px`,
      overflow: 'auto',
      '::-webkit-scrollbar': {
        background: theme.bgPrimaryColor,
      },
      '::-webkit-scrollbar-thumb': {
        background: theme.fgSecondaryColor,
        borderRadius: 20,
        border: `3px solid ${theme.bgPrimaryColor}`,
        ':hover': {
          background: theme.fgPrimaryColor,
        },
      },
    },
    stackLine: {
      whiteSpace: 'nowrap',
    },
    stackFileLine: {
      color: theme.fgSecondaryColor,
    },
    statsTable: {
      display: 'grid',
      gridTemplateColumns: '1fr 1fr',
      gridTemplateRows: `repeat(3, ${FontSize.LABEL + 10}px)`,
      gridGap: '1px 1px',
      textAlign: 'center',
      paddingRight: 1,
    },
    statsTableHeader: {
      gridColumn: '1 / 3',
    },
    statsTableCell: {
      position: 'relative',
      display: 'flex',
      justifyContent: 'center',
      alignItems: 'center',
    },
    thisInstanceCell: {
      background: theme.selectionPrimaryColor,
      color: theme.altFgPrimaryColor,
    },
    allInstancesCell: {
      background: theme.selectionSecondaryColor,
      color: theme.altFgPrimaryColor,
    },
    barDisplay: {
      position: 'absolute',
      top: 0,
      left: 0,
      background: 'rgba(0, 0, 0, 0.2)',
      width: '100%',
    },
  }),
)
