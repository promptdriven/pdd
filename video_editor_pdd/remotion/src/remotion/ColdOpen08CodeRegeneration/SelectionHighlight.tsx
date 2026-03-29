import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  SELECTION_COLOR,
  SELECTION_OPACITY,
  GUTTER_WIDTH,
  LINE_HEIGHT,
  CODE_PADDING_TOP,
  CANVAS_WIDTH,
  ORIGINAL_LINE_COUNT,
  PHASE_SELECT_START,
  PHASE_SELECT_END,
  PHASE_DELETE_START,
  PHASE_DELETE_END,
} from './constants';

/**
 * Renders the blue selection highlight that sweeps across the patched code,
 * then contracts/vanishes on delete.
 */
export const SelectionHighlight: React.FC = () => {
  const frame = useCurrentFrame();

  // How many lines are selected at this frame
  const selectedLines = Math.min(
    Math.floor(
      interpolate(
        frame,
        [PHASE_SELECT_START, PHASE_SELECT_END],
        [0, ORIGINAL_LINE_COUNT],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    ),
    ORIGINAL_LINE_COUNT
  );

  // During delete phase, fade out the selection
  const deleteOpacity = interpolate(
    frame,
    [PHASE_DELETE_START, PHASE_DELETE_END],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // Don't render after delete
  if (frame >= PHASE_DELETE_END) return null;

  return (
    <>
      {Array.from({ length: selectedLines }, (_, i) => (
        <div
          key={i}
          style={{
            position: 'absolute',
            top: CODE_PADDING_TOP + i * LINE_HEIGHT,
            left: GUTTER_WIDTH,
            width: CANVAS_WIDTH - GUTTER_WIDTH,
            height: LINE_HEIGHT,
            backgroundColor: SELECTION_COLOR,
            opacity: SELECTION_OPACITY * deleteOpacity,
          }}
        />
      ))}
    </>
  );
};

export default SelectionHighlight;
