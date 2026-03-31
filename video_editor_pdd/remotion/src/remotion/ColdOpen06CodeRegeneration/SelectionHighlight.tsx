import React from "react";
import {
  SELECTION_COLOR,
  SELECTION_OPACITY,
  CODE_LINE_HEIGHT,
  CODE_TOP_PADDING,
  GUTTER_WIDTH,
  CANVAS_WIDTH,
} from "./constants";

interface SelectionHighlightProps {
  /** Number of lines selected (1-based count). */
  totalLines: number;
  /** 0–1 progress of the selection sweep (0 = no lines selected, 1 = all selected). */
  progress: number;
}

/**
 * Blue selection highlight that sweeps top-to-bottom over code lines.
 */
const SelectionHighlight: React.FC<SelectionHighlightProps> = ({
  totalLines,
  progress,
}) => {
  const linesSelected = Math.floor(progress * totalLines);
  if (linesSelected <= 0) return null;

  const highlightHeight = linesSelected * CODE_LINE_HEIGHT;

  return (
    <div
      style={{
        position: "absolute",
        top: CODE_TOP_PADDING,
        left: GUTTER_WIDTH,
        width: CANVAS_WIDTH - GUTTER_WIDTH,
        height: highlightHeight,
        backgroundColor: SELECTION_COLOR,
        opacity: SELECTION_OPACITY,
        pointerEvents: "none",
      }}
    />
  );
};

export default SelectionHighlight;
