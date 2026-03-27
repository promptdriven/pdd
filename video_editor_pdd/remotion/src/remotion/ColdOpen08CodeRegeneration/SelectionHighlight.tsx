import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';

/**
 * Blue selection sweep that highlights lines top-to-bottom.
 * Lines sweep at 5 lines/frame from frame 0 → 8.
 */

interface SelectionHighlightProps {
  totalLines: number;
  lineHeight: number;
  gutterWidth: number;
  paddingTop: number;
  selectionColor: string;
  selectionOpacity: number;
  sweepStartFrame: number;
  sweepEndFrame: number;
}

export const SelectionHighlight: React.FC<SelectionHighlightProps> = ({
  totalLines,
  lineHeight,
  gutterWidth,
  paddingTop,
  selectionColor,
  selectionOpacity,
  sweepStartFrame,
  sweepEndFrame,
}) => {
  const frame = useCurrentFrame();

  // How many lines are highlighted so far (5 lines per frame, linear)
  const sweepProgress = interpolate(
    frame,
    [sweepStartFrame, sweepEndFrame],
    [0, totalLines],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const visibleLines = Math.floor(sweepProgress);
  if (visibleLines <= 0) return null;

  return (
    <>
      {Array.from({ length: Math.min(visibleLines, totalLines) }).map((_, i) => (
        <div
          key={i}
          style={{
            position: 'absolute',
            top: paddingTop + i * lineHeight,
            left: gutterWidth,
            right: 40,
            height: lineHeight,
            backgroundColor: selectionColor,
            opacity: selectionOpacity,
          }}
        />
      ))}
    </>
  );
};
