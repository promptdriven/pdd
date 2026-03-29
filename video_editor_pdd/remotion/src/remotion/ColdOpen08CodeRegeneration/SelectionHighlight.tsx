import React from 'react';
import {
  CODE_LINE_HEIGHT,
  GUTTER_WIDTH,
  SELECTION_COLOR,
  SELECTION_OPACITY,
} from './constants';

interface SelectionHighlightProps {
  /** How many lines (from line 1) are currently selected */
  selectedLineCount: number;
  /** Total lines in the editor code */
  totalLines: number;
}

const SelectionHighlight: React.FC<SelectionHighlightProps> = ({
  selectedLineCount,
  totalLines,
}) => {
  if (selectedLineCount <= 0) return null;

  const count = Math.min(selectedLineCount, totalLines);

  return (
    <>
      {Array.from({ length: count }, (_, i) => (
        <div
          key={i}
          style={{
            position: 'absolute',
            top: i * CODE_LINE_HEIGHT,
            left: GUTTER_WIDTH,
            right: 0,
            height: CODE_LINE_HEIGHT,
            backgroundColor: SELECTION_COLOR,
            opacity: SELECTION_OPACITY,
            pointerEvents: 'none',
          }}
        />
      ))}
    </>
  );
};

export default SelectionHighlight;
