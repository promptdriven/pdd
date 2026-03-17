// Part5CompoundReturns07EconomicsCrossingCallback.tsx
// The sock economics chart from Part 1 returns and morphs into code economics.
// A full-circle narrative callback showing the same crossing-point economics.

import React, { useMemo } from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import {
  CANVAS,
  CHART,
  COLORS,
  FRAMES,
  INITIAL_DATA,
  FINAL_DATA,
  Y_RANGE,
} from './constants';
import { ChartAxes } from './ChartAxes';
import { AnimatedLine } from './AnimatedLine';
import { ShadedAreas } from './ShadedAreas';
import { CrossingPoint } from './CrossingPoint';
import { DarningNeedle } from './DarningNeedle';

// ---------- helpers ----------

/** Linearly interpolate between two numbers */
const lerp = (a: number, b: number, t: number): number => a + (b - a) * t;

/** Interpolate a data point array: lerp each point's x and y */
const lerpDataArray = (
  a: readonly { x: number; y: number }[],
  b: readonly { x: number; y: number }[],
  t: number,
): { x: number; y: number }[] => {
  // Use the longer array as base, padding shorter with its last point
  const maxLen = Math.max(a.length, b.length);
  const result: { x: number; y: number }[] = [];
  for (let i = 0; i < maxLen; i++) {
    const ai = i < a.length ? a[i] : a[a.length - 1];
    const bi = i < b.length ? b[i] : b[b.length - 1];
    result.push({
      x: lerp(ai.x, bi.x, t),
      y: lerp(ai.y, bi.y, t),
    });
  }
  return result;
};

/** Interpolate between two label arrays (cross-fade text) */
const lerpLabels = (
  a: readonly string[],
  b: readonly string[],
  t: number,
): string[] => {
  const maxLen = Math.max(a.length, b.length);
  const result: string[] = [];
  for (let i = 0; i < maxLen; i++) {
    const ai = i < a.length ? a[i] : '';
    const bi = i < b.length ? b[i] : '';
    // Simple approach: switch at t=0.5 threshold
    result.push(t < 0.5 ? ai : bi);
  }
  return result;
};

/** Text morph: letter-by-letter reveal of target over source */
const morphText = (from: string, to: string, t: number): string => {
  if (t <= 0) return from;
  if (t >= 1) return to;
  const maxLen = Math.max(from.length, to.length);
  const charsRevealed = Math.floor(t * maxLen);
  // Build string: first charsRevealed chars from 'to', rest from 'from'
  let result = '';
  for (let i = 0; i < maxLen; i++) {
    if (i < charsRevealed) {
      result += i < to.length ? to[i] : '';
    } else {
      result += i < from.length ? from[i] : '';
    }
  }
  return result;
};

/** Map crossing year to pixel X position */
const crossingToPixelX = (
  crossingYear: number,
  xRange: [number, number],
): number => {
  const frac = (crossingYear - xRange[0]) / (xRange[1] - xRange[0]);
  return CHART.left + frac * CHART.width;
};

/** Get crossing Y in pixels (both lines meet at approximately same value) */
const crossingToPixelY = (
  crossingYear: number,
  risingData: readonly { x: number; y: number }[],
): number => {
  // Interpolate y from rising data at crossing year
  for (let i = 0; i < risingData.length - 1; i++) {
    if (crossingYear >= risingData[i].x && crossingYear <= risingData[i + 1].x) {
      const t =
        (crossingYear - risingData[i].x) /
        (risingData[i + 1].x - risingData[i].x);
      const yVal = risingData[i].y + t * (risingData[i + 1].y - risingData[i].y);
      return CHART.top + CHART.height - (yVal / Y_RANGE.max) * CHART.height;
    }
  }
  return CHART.top + CHART.height / 2;
};

// ---------- default props ----------

export const defaultPart5CompoundReturns07EconomicsCrossingCallbackProps = {};

// ---------- main component ----------

export const Part5CompoundReturns07EconomicsCrossingCallback: React.FC = () => {
  const frame = useCurrentFrame();

  // ---- Phase 1: Chart fade-in (0-30) ----
  const fadeInOpacity = interpolate(
    frame,
    [FRAMES.fadeInStart, FRAMES.fadeInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // ---- Phase 3: Morph progress (60-150) ----
  const morphT = interpolate(
    frame,
    [FRAMES.morphStart, FRAMES.morphEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  // ---- Phase 4: Post-crossing relabel (150-210) ----
  const relabelT = interpolate(
    frame,
    [FRAMES.relabelStart, FRAMES.relabelEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  // ---- Phase 5: Needle appear (210+) ----
  const needleOpacity = interpolate(frame, [FRAMES.needleStart, FRAMES.needleStart + 5], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // ---- Compute interpolated chart state ----
  const currentXRange: [number, number] = [
    lerp(INITIAL_DATA.xRange[0], FINAL_DATA.xRange[0], morphT),
    lerp(INITIAL_DATA.xRange[1], FINAL_DATA.xRange[1], morphT),
  ];

  const currentXLabels = lerpLabels(
    INITIAL_DATA.xLabels,
    FINAL_DATA.xLabels,
    morphT,
  );

  const currentLaborData = useMemo(
    () => lerpDataArray(INITIAL_DATA.laborData, FINAL_DATA.laborData, morphT),
    [morphT],
  );

  const currentSockData = useMemo(
    () => lerpDataArray(INITIAL_DATA.sockData, FINAL_DATA.sockData, morphT),
    [morphT],
  );

  const currentCrossingYear = lerp(
    INITIAL_DATA.crossingYear,
    FINAL_DATA.crossingYear,
    morphT,
  );

  // Text morph for labels
  const currentLine1Label = morphText(
    INITIAL_DATA.line1Label,
    FINAL_DATA.line1Label,
    morphT,
  );
  const currentLine2Label = morphText(
    INITIAL_DATA.line2Label,
    FINAL_DATA.line2Label,
    morphT,
  );
  const currentCrossingLabel = morphText(
    INITIAL_DATA.crossingLabel,
    FINAL_DATA.crossingLabel,
    morphT,
  );

  // Post-crossing label morphs in relabel phase
  const currentPostLabel = morphText(
    INITIAL_DATA.postCrossingLabel,
    FINAL_DATA.postCrossingLabel,
    relabelT,
  );

  // Crossing point pixel position
  const crossingPx = crossingToPixelX(currentCrossingYear, currentXRange);
  const crossingPy = crossingToPixelY(currentCrossingYear, currentLaborData);

  // Pulse starts at frame 30
  const isPulsing = frame >= FRAMES.pulseStart;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.BG,
        overflow: 'hidden',
      }}
    >
      {/* Chart grid and axes */}
      <ChartAxes xLabels={currentXLabels} opacity={fadeInOpacity} />

      {/* Shaded areas between lines */}
      <ShadedAreas
        risingData={currentLaborData}
        fallingData={currentSockData}
        xRange={currentXRange}
        crossingYear={currentCrossingYear}
        postLabel={currentPostLabel}
        opacity={fadeInOpacity}
      />

      {/* Amber line: Labor / Patching cost */}
      <AnimatedLine
        data={currentLaborData}
        xRange={currentXRange}
        color={COLORS.amber}
        label={currentLine1Label}
        opacity={fadeInOpacity}
      />

      {/* Blue line: Sock / Generation cost */}
      <AnimatedLine
        data={currentSockData}
        xRange={currentXRange}
        color={COLORS.blue}
        label={currentLine2Label}
        opacity={fadeInOpacity}
      />

      {/* Crossing point with pulse */}
      <CrossingPoint
        cx={crossingPx}
        cy={crossingPy}
        label={currentCrossingLabel}
        pulsing={isPulsing}
        opacity={fadeInOpacity}
      />

      {/* Darning needle with strikethrough — appears at frame 210 */}
      <Sequence from={FRAMES.needleStart}>
        <DarningNeedle opacity={needleOpacity} />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns07EconomicsCrossingCallback;
