import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { GridLines } from "./GridLines";
import { AxisLabels } from "./AxisLabels";
import { QuadrantFill } from "./QuadrantFill";
import { NeutralQuadrants } from "./NeutralQuadrants";
import { InsightText } from "./InsightText";
import {
  BG_COLOR,
  GRID_SIZE,
  CELL_SIZE,
  GRID_LEFT,
  GRID_TOP,
  GRID_LINE_COLOR,
  GRID_LINE_WIDTH,
  GREEN_QUADRANT,
  GREEN_FILL_OPACITY,
  GREEN_GLOW_OPACITY,
  RED_QUADRANT,
  RED_FILL_OPACITY,
  RED_GLOW_OPACITY,
  NEUTRAL_FILL,
  NEUTRAL_FILL_OPACITY,
  AXIS_LABEL_COLOR,
  AXIS_LABEL_SIZE,
  QUADRANT_LABEL_SIZE,
  INSIGHT_COLOR,
  INSIGHT_SIZE,
  INSIGHT_Y,
  GRID_DRAW_START,
  GRID_DRAW_END,
  GREEN_QUADRANT_START,
  GREEN_QUADRANT_END,
  RED_QUADRANT_START,
  RED_QUADRANT_END,
  INSIGHT_FADE_START,
  INSIGHT_FADE_DURATION,
  X_LABELS,
  Y_LABELS,
  GREEN_LABEL_TEXT,
  RED_LABEL_TEXT,
  INSIGHT_TEXT,
  DURATION_FRAMES,
} from "./constants";

export const defaultPart1Economics09TwoByTwoGridProps = {};

export const Part1Economics09TwoByTwoGrid: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Title at the top */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <div
          style={{
            position: "absolute",
            top: 60,
            left: 0,
            width: 1920,
            display: "flex",
            justifyContent: "center",
          }}
        >
          <div
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 28,
              fontWeight: 600,
              color: "#E2E8F0",
              letterSpacing: "-0.02em",
              opacity: 0.9,
            }}
          >
            Study Reconciliation Grid
          </div>
        </div>
      </Sequence>

      {/* Neutral quadrant fills — appear with grid */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <NeutralQuadrants
          gridLeft={GRID_LEFT}
          gridTop={GRID_TOP}
          cellSize={CELL_SIZE}
          fillColor={NEUTRAL_FILL}
          fillOpacity={NEUTRAL_FILL_OPACITY}
          fadeStart={GRID_DRAW_START + 15}
          fadeEnd={GRID_DRAW_END}
        />
      </Sequence>

      {/* Grid lines draw in */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <GridLines
          gridLeft={GRID_LEFT}
          gridTop={GRID_TOP}
          gridSize={GRID_SIZE}
          cellSize={CELL_SIZE}
          lineColor={GRID_LINE_COLOR}
          lineWidth={GRID_LINE_WIDTH}
          drawStart={GRID_DRAW_START}
          drawEnd={GRID_DRAW_END}
        />
      </Sequence>

      {/* Axis labels fade in with grid */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <AxisLabels
          gridLeft={GRID_LEFT}
          gridTop={GRID_TOP}
          gridSize={GRID_SIZE}
          cellSize={CELL_SIZE}
          xLabels={X_LABELS}
          yLabels={Y_LABELS}
          labelColor={AXIS_LABEL_COLOR}
          labelSize={AXIS_LABEL_SIZE}
          fadeStart={GRID_DRAW_START + 15}
          fadeEnd={GRID_DRAW_END + 10}
        />
      </Sequence>

      {/* Top-left quadrant: GREEN (GitHub study: +55%) */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <QuadrantFill
          x={GRID_LEFT}
          y={GRID_TOP}
          size={CELL_SIZE}
          color={GREEN_QUADRANT}
          fillOpacity={GREEN_FILL_OPACITY}
          glowOpacity={GREEN_GLOW_OPACITY}
          label={GREEN_LABEL_TEXT}
          labelColor={GREEN_QUADRANT}
          labelSize={QUADRANT_LABEL_SIZE}
          animStart={GREEN_QUADRANT_START}
          animEnd={GREEN_QUADRANT_END}
        />
      </Sequence>

      {/* Bottom-right quadrant: RED (METR study: −19%) */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <QuadrantFill
          x={GRID_LEFT + CELL_SIZE}
          y={GRID_TOP + CELL_SIZE}
          size={CELL_SIZE}
          color={RED_QUADRANT}
          fillOpacity={RED_FILL_OPACITY}
          glowOpacity={RED_GLOW_OPACITY}
          label={RED_LABEL_TEXT}
          labelColor={RED_QUADRANT}
          labelSize={QUADRANT_LABEL_SIZE}
          animStart={RED_QUADRANT_START}
          animEnd={RED_QUADRANT_END}
        />
      </Sequence>

      {/* Key insight text */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <InsightText
          text={INSIGHT_TEXT}
          color={INSIGHT_COLOR}
          fontSize={INSIGHT_SIZE}
          y={INSIGHT_Y}
          fadeStart={INSIGHT_FADE_START}
          fadeDuration={INSIGHT_FADE_DURATION}
        />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics09TwoByTwoGrid;
