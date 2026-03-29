import React from "react";
import {
  AbsoluteFill,
  Sequence,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  AXES_START,
  CURVE_START,
  DOT_APPEAR_FRAME,
  LEFT_CALLOUT_START,
  RIGHT_CALLOUT_START,
  FADEOUT_START,
  FADEOUT_DURATION,
  TOTAL_FRAMES,
} from "./constants";
import { GridLines } from "./GridLines";
import { ChartAxes } from "./ChartAxes";
import { AnimatedCurve } from "./AnimatedCurve";
import { ZoneShading } from "./ZoneShading";
import { TraversingDot } from "./TraversingDot";
import { Callout } from "./Callout";

export const defaultPart4PrecisionTradeoff03PrecisionTradeoffCurveProps = {};

export const Part4PrecisionTradeoff03PrecisionTradeoffCurve: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade out in the last 60 frames
  const fadeOutOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
      }}
    >
      <AbsoluteFill style={{ opacity: fadeOutOpacity }}>
        {/* Grid lines — fade in with axes */}
        <Sequence from={AXES_START} durationInFrames={TOTAL_FRAMES}>
          <GridLines />
        </Sequence>

        {/* Chart axes — draw from origin */}
        <Sequence from={AXES_START} durationInFrames={TOTAL_FRAMES}>
          <ChartAxes />
        </Sequence>

        {/* Zone shading — fills beneath curve as it draws */}
        <Sequence
          from={CURVE_START}
          durationInFrames={TOTAL_FRAMES - CURVE_START}
        >
          <ZoneShading />
        </Sequence>

        {/* Inverse curve — draws left to right */}
        <Sequence
          from={CURVE_START}
          durationInFrames={TOTAL_FRAMES - CURVE_START}
        >
          <AnimatedCurve />
        </Sequence>

        {/* Traversing dot — appears at left, then moves along curve */}
        <Sequence
          from={DOT_APPEAR_FRAME}
          durationInFrames={TOTAL_FRAMES - DOT_APPEAR_FRAME}
        >
          <TraversingDot />
        </Sequence>

        {/* Left callout: "50-line prompt / Every edge case specified" */}
        <Sequence
          from={LEFT_CALLOUT_START}
          durationInFrames={TOTAL_FRAMES - LEFT_CALLOUT_START}
        >
          <Callout
            dataX={3}
            text={"50-line prompt\nEvery edge case specified"}
            color="#D9944A"
            anchor="above-right"
          />
        </Sequence>

        {/* Right callout: "10-line prompt / Tests handle constraints" */}
        <Sequence
          from={RIGHT_CALLOUT_START}
          durationInFrames={TOTAL_FRAMES - RIGHT_CALLOUT_START}
        >
          <Callout
            dataX={45}
            text={"10-line prompt\nTests handle constraints"}
            color="#4A90D9"
            anchor="above-left"
          />
        </Sequence>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff03PrecisionTradeoffCurve;
