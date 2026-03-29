import React from "react";
import {
  AbsoluteFill,
  Sequence,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import GridLines from "./GridLines";
import QuadrantFill from "./QuadrantFill";
import {
  BACKGROUND_COLOR,
  GRID_SIZE,
  CELL_SIZE,
  GRID_LEFT,
  GRID_TOP,
  GRID_LINE_COLOR,
  GRID_LINE_WIDTH,
  AXIS_LABEL_COLOR,
  AXIS_LABEL_SIZE,
  GREEN_QUADRANT_COLOR,
  GREEN_FILL_OPACITY,
  GREEN_GLOW_OPACITY,
  RED_QUADRANT_COLOR,
  RED_FILL_OPACITY,
  RED_GLOW_OPACITY,
  NEUTRAL_COLOR,
  NEUTRAL_FILL_OPACITY,
  QUADRANT_LABEL_SIZE,
  INSIGHT_TEXT_COLOR,
  INSIGHT_TEXT_SIZE,
  INSIGHT_Y,
  GRID_DRAW_END,
  GREEN_QUADRANT_START,
  QUADRANT_FILL_DURATION,
  RED_QUADRANT_START,
  INSIGHT_FADE_START,
  INSIGHT_FADE_DURATION,
  TOTAL_FRAMES,
  FRAMES_PER_CHAR,
  GRID_DRAW_DURATION,
} from "./constants";

export const defaultPart1Economics09TwoByTwoGridProps = {};

/** Neutral quadrant fill — non-animated, fades in with grid */
const NeutralQuadrant: React.FC<{
  left: number;
  top: number;
  size: number;
  color: string;
  fillOpacity: number;
}> = ({ left, top, size, color, fillOpacity }) => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [0, GRID_DRAW_DURATION], [0, fillOpacity], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        left,
        top,
        width: size,
        height: size,
        backgroundColor: color,
        opacity,
      }}
    />
  );
};

/** Insight text that fades in */
const InsightText: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [0, INSIGHT_FADE_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: INSIGHT_Y,
        width: 1920,
        display: "flex",
        justifyContent: "center",
        opacity,
      }}
    >
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: INSIGHT_TEXT_SIZE,
          fontWeight: 400,
          color: INSIGHT_TEXT_COLOR,
          textAlign: "center",
          maxWidth: 800,
          lineHeight: 1.5,
        }}
      >
        Every study is correct. They just measured different quadrants.
      </div>
    </div>
  );
};

/** Section title at the top */
const SectionTitle: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [10, 40], [0, 0.85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        top: 50,
        width: 1920,
        display: "flex",
        justifyContent: "center",
        opacity,
      }}
    >
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 28,
          fontWeight: 600,
          color: "#E2E8F0",
          textAlign: "center",
          letterSpacing: 0.5,
        }}
      >
        Reconciling the Studies
      </div>
    </div>
  );
};

export const Part1Economics09TwoByTwoGrid: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Section title */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <SectionTitle />
      </Sequence>

      {/* Neutral quadrants (top-right, bottom-left) — appear with grid */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <NeutralQuadrant
          left={GRID_LEFT + CELL_SIZE}
          top={GRID_TOP}
          size={CELL_SIZE}
          color={NEUTRAL_COLOR}
          fillOpacity={NEUTRAL_FILL_OPACITY}
        />
        <NeutralQuadrant
          left={GRID_LEFT}
          top={GRID_TOP + CELL_SIZE}
          size={CELL_SIZE}
          color={NEUTRAL_COLOR}
          fillOpacity={NEUTRAL_FILL_OPACITY}
        />
      </Sequence>

      {/* Grid lines and axis labels — draw from frame 0 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <GridLines
          gridLeft={GRID_LEFT}
          gridTop={GRID_TOP}
          gridSize={GRID_SIZE}
          lineColor={GRID_LINE_COLOR}
          lineWidth={GRID_LINE_WIDTH}
          axisLabelColor={AXIS_LABEL_COLOR}
          axisLabelSize={AXIS_LABEL_SIZE}
          drawDuration={GRID_DRAW_END}
        />
      </Sequence>

      {/* Top-left quadrant: Green (GitHub study +55%) */}
      <Sequence
        from={GREEN_QUADRANT_START}
        durationInFrames={TOTAL_FRAMES - GREEN_QUADRANT_START}
      >
        <QuadrantFill
          quadrantLeft={GRID_LEFT}
          quadrantTop={GRID_TOP}
          cellSize={CELL_SIZE}
          accentColor={GREEN_QUADRANT_COLOR}
          fillOpacity={GREEN_FILL_OPACITY}
          glowOpacity={GREEN_GLOW_OPACITY}
          labelText="GitHub study: +55%"
          labelColor={GREEN_QUADRANT_COLOR}
          labelSize={QUADRANT_LABEL_SIZE}
          animateInDuration={QUADRANT_FILL_DURATION}
          framesPerChar={FRAMES_PER_CHAR}
        />
      </Sequence>

      {/* Bottom-right quadrant: Red (METR study −19%) */}
      <Sequence
        from={RED_QUADRANT_START}
        durationInFrames={TOTAL_FRAMES - RED_QUADRANT_START}
      >
        <QuadrantFill
          quadrantLeft={GRID_LEFT + CELL_SIZE}
          quadrantTop={GRID_TOP + CELL_SIZE}
          cellSize={CELL_SIZE}
          accentColor={RED_QUADRANT_COLOR}
          fillOpacity={RED_FILL_OPACITY}
          glowOpacity={RED_GLOW_OPACITY}
          labelText="METR study: −19%"
          labelColor={RED_QUADRANT_COLOR}
          labelSize={QUADRANT_LABEL_SIZE}
          animateInDuration={QUADRANT_FILL_DURATION}
          framesPerChar={FRAMES_PER_CHAR}
        />
      </Sequence>

      {/* Insight text */}
      <Sequence
        from={INSIGHT_FADE_START}
        durationInFrames={TOTAL_FRAMES - INSIGHT_FADE_START}
      >
        <InsightText />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics09TwoByTwoGrid;
