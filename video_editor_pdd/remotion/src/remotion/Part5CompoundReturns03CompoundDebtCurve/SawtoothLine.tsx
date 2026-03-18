import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CHART_LEFT,
  CHART_RIGHT,
  REGEN_COLOR,
  SAWTOOTH_BASELINE_Y,
  SAWTOOTH_PEAK_Y,
  SAWTOOTH_TEETH,
  SAWTOOTH_DURATION,
} from './constants';

/**
 * Build sawtooth path: flat baseline with sharp triangular peaks.
 * Each tooth: flat run → sharp rise (30px) → quick fall (10px) → back to baseline.
 */
function buildSawtoothPath(): { path: string; totalLength: number } {
  const startX = CHART_LEFT;
  const endX = CHART_RIGHT;
  const totalWidth = endX - startX;
  const toothWidth = totalWidth / SAWTOOTH_TEETH;
  const flatRun = toothWidth - 40; // remaining width after peak shape
  const riseWidth = 30;
  const fallWidth = 10;

  let d = `M ${startX} ${SAWTOOTH_BASELINE_Y}`;
  let length = 0;

  for (let i = 0; i < SAWTOOTH_TEETH; i++) {
    const toothStart = startX + i * toothWidth;

    // Flat segment
    const flatEnd = toothStart + flatRun;
    d += ` L ${flatEnd} ${SAWTOOTH_BASELINE_Y}`;
    length += flatRun;

    // Rise to peak
    const peakX = flatEnd + riseWidth;
    d += ` L ${peakX} ${SAWTOOTH_PEAK_Y}`;
    length += Math.sqrt(riseWidth * riseWidth + (SAWTOOTH_BASELINE_Y - SAWTOOTH_PEAK_Y) ** 2);

    // Fall back to baseline
    const fallEndX = peakX + fallWidth;
    d += ` L ${fallEndX} ${SAWTOOTH_BASELINE_Y}`;
    length += Math.sqrt(fallWidth * fallWidth + (SAWTOOTH_BASELINE_Y - SAWTOOTH_PEAK_Y) ** 2);
  }

  return { path: d, totalLength: length };
}

/**
 * Build dashed vertical lines at each sawtooth reset point.
 */
function getResetXPositions(): number[] {
  const totalWidth = CHART_RIGHT - CHART_LEFT;
  const toothWidth = totalWidth / SAWTOOTH_TEETH;
  const positions: number[] = [];

  for (let i = 1; i < SAWTOOTH_TEETH; i++) {
    positions.push(CHART_LEFT + i * toothWidth);
  }
  return positions;
}

export const SawtoothLine: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(frame, [0, SAWTOOTH_DURATION], [0, 1], {
    extrapolateRight: 'clamp',
  });

  const { path, totalLength } = buildSawtoothPath();
  const visibleLength = drawProgress * totalLength;

  const resetPositions = getResetXPositions();

  // Label opacity — appears as line draws near end
  const labelOpacity = interpolate(frame, [SAWTOOTH_DURATION - 30, SAWTOOTH_DURATION], [0, 0.5], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Reset line opacity
  const resetLineOpacity = interpolate(frame, [0, SAWTOOTH_DURATION * 0.3], [0, 0.08], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <>
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* Dashed vertical reset lines */}
        {resetPositions.map((x, i) => (
          <line
            key={`reset-${i}`}
            x1={x}
            y1={SAWTOOTH_PEAK_Y - 20}
            x2={x}
            y2={SAWTOOTH_BASELINE_Y + 20}
            stroke={REGEN_COLOR}
            strokeWidth={1}
            strokeDasharray="4 4"
            opacity={resetLineOpacity}
          />
        ))}

        {/* Sawtooth line */}
        <path
          d={path}
          fill="none"
          stroke={REGEN_COLOR}
          strokeWidth={2}
          strokeDasharray={totalLength}
          strokeDashoffset={totalLength - visibleLength}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
      </svg>

      {/* Label at endpoint */}
      <div
        style={{
          position: 'absolute',
          left: CHART_RIGHT + 15,
          top: SAWTOOTH_BASELINE_Y - 20,
          fontFamily: 'Inter, sans-serif',
          fontSize: 12,
          color: REGEN_COLOR,
          opacity: labelOpacity,
          maxWidth: 180,
          lineHeight: 1.3,
        }}
      >
        Regeneration cost
        <br />
        <span style={{ fontSize: 10, opacity: 0.7 }}>(resets each cycle)</span>
      </div>
    </>
  );
};
