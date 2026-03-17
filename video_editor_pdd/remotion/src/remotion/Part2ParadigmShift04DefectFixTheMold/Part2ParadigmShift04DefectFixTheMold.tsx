import React from "react";
import { AbsoluteFill, useCurrentFrame } from "remotion";
import { MoldDiagram } from "./MoldDiagram";
import { EjectedPart } from "./EjectedPart";
import { DefectHighlight } from "./DefectHighlight";
import { RejectedPatch } from "./RejectedPatch";
import { MoldAdjustment } from "./MoldAdjustment";
import { FixedPartsSequence } from "./FixedPartsSequence";
import {
  BG_COLOR,
  GRID_SPACING,
  GRID_COLOR,
  GRID_OPACITY,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  PART_EJECT_START,
  DEFECT_PULSE_START,
  GHOST_TOOL_START,
  REJECTED_FADE_END,
  WALL_ADJUST_START,
  FIXED_PARTS_START,
  DISSOLVE_START,
} from "./constants";

export const defaultPart2ParadigmShift04DefectFixTheMoldProps = {};

export const Part2ParadigmShift04DefectFixTheMold: React.FC = () => {
  const frame = useCurrentFrame();

  // Grid lines for drafting aesthetic
  const gridLinesVertical: number[] = [];
  for (let x = 0; x <= CANVAS_WIDTH; x += GRID_SPACING) {
    gridLinesVertical.push(x);
  }
  const gridLinesHorizontal: number[] = [];
  for (let y = 0; y <= CANVAS_HEIGHT; y += GRID_SPACING) {
    gridLinesHorizontal.push(y);
  }

  // Phase flags based on frame
  const showEjectedPart = frame >= PART_EJECT_START;
  const showDefect = frame >= DEFECT_PULSE_START;
  const showRejectedPatch = frame >= GHOST_TOOL_START && frame < REJECTED_FADE_END;
  const showMoldAdjustment = frame >= WALL_ADJUST_START;
  const showFixedParts = frame >= FIXED_PARTS_START;
  const showDissolve = frame >= DISSOLVE_START;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Drafting grid */}
      <svg
        width={CANVAS_WIDTH}
        height={CANVAS_HEIGHT}
        style={{ position: "absolute", left: 0, top: 0 }}
      >
        {gridLinesVertical.map((x) => (
          <line
            key={`gv-${x}`}
            x1={x}
            y1={0}
            x2={x}
            y2={CANVAS_HEIGHT}
            stroke={GRID_COLOR}
            strokeWidth={1}
            strokeOpacity={GRID_OPACITY}
          />
        ))}
        {gridLinesHorizontal.map((y) => (
          <line
            key={`gh-${y}`}
            x1={0}
            y1={y}
            x2={CANVAS_WIDTH}
            y2={y}
            stroke={GRID_COLOR}
            strokeWidth={1}
            strokeOpacity={GRID_OPACITY}
          />
        ))}
      </svg>

      {/* Mold diagram — always visible, draws in Act 0 */}
      <MoldDiagram showAdjustment={showMoldAdjustment} />

      {/* Original ejected part (defective) */}
      {showEjectedPart && (
        <EjectedPart showDefect={showDefect} dissolve={showDissolve} />
      )}

      {/* Defect highlight — red pulse, magnifying glass, label */}
      {showDefect && frame < REJECTED_FADE_END && (
        <DefectHighlight />
      )}

      {/* Rejected "patch the part" approach — ghost tool + red X */}
      {showRejectedPatch && (
        <RejectedPatch />
      )}

      {/* Mold wall adjustment — cursor, amber glow, label */}
      {showMoldAdjustment && (
        <MoldAdjustment />
      )}

      {/* Fixed parts ejecting with green checkmarks */}
      {showFixedParts && (
        <FixedPartsSequence />
      )}
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift04DefectFixTheMold;
