import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';

/**
 * MoldCycleAnimation renders a 2D cross-section of two mold halves
 * opening and closing with a plastic part ejecting each cycle.
 * The cycle speed accelerates over the duration.
 */

const MOLD_COLOR = '#78909C';
const PART_COLOR = '#D9944A';
const MOLD_CENTER_X = 700;
const MOLD_CENTER_Y = 450;
const MOLD_HALF_WIDTH = 200;
const MOLD_HALF_HEIGHT = 280;
const MOLD_GAP_OPEN = 120;
const MOLD_GAP_CLOSED = 2;
const PART_WIDTH = 80;
const PART_HEIGHT = 60;
const TOTAL_FRAMES = 300;
const START_FRAMES_PER_CYCLE = 60;
const END_FRAMES_PER_CYCLE = 6;

export const MoldCycleAnimation: React.FC = () => {
  const frame = useCurrentFrame();

  // Calculate current cycle speed — accelerates from 60 to 6 frames/cycle
  const cycleSpeed = interpolate(
    frame,
    [0, TOTAL_FRAMES],
    [START_FRAMES_PER_CYCLE, END_FRAMES_PER_CYCLE],
    {
      easing: Easing.in(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // Compute cumulative cycle progress by integrating the speed curve
  // At each frame, figure out where we are in the current cycle (0..1)
  // Use a simulated approach: compute total elapsed "cycles" up to this frame
  let totalCycleProgress = 0;
  for (let f = 0; f < frame; f++) {
    const speed = interpolate(
      f,
      [0, TOTAL_FRAMES],
      [START_FRAMES_PER_CYCLE, END_FRAMES_PER_CYCLE],
      {
        easing: Easing.in(Easing.quad),
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      },
    );
    totalCycleProgress += 1 / speed;
  }

  const cyclePhase = totalCycleProgress % 1; // 0..1 within current cycle

  // Cycle phases:
  // 0.0 - 0.3: Mold closing
  // 0.3 - 0.5: Mold closed (injection)
  // 0.5 - 0.7: Mold opening
  // 0.7 - 1.0: Part eject + reset

  let moldGap: number;
  let partEjectY = 0;
  let partVisible = false;
  let partOpacity = 1;

  if (cyclePhase < 0.3) {
    // Closing
    const t = cyclePhase / 0.3;
    moldGap = interpolate(t, [0, 1], [MOLD_GAP_OPEN, MOLD_GAP_CLOSED]);
  } else if (cyclePhase < 0.5) {
    // Closed (injection phase)
    moldGap = MOLD_GAP_CLOSED;
  } else if (cyclePhase < 0.7) {
    // Opening
    const t = (cyclePhase - 0.5) / 0.2;
    moldGap = interpolate(t, [0, 1], [MOLD_GAP_CLOSED, MOLD_GAP_OPEN]);
  } else {
    // Part ejects
    moldGap = MOLD_GAP_OPEN;
    partVisible = true;
    const t = (cyclePhase - 0.7) / 0.3;
    const easedT = Easing.out(Easing.quad)(t);
    partEjectY = easedT * 200; // eject upward
    partOpacity = interpolate(t, [0, 0.7, 1], [1, 1, 0.3]);
  }

  // Also show part being formed during injection phase
  const showForming = cyclePhase >= 0.3 && cyclePhase < 0.5;
  const formingOpacity = interpolate(
    cyclePhase,
    [0.3, 0.5],
    [0.2, 0.8],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Mold glow effect at high speed
  const speedRatio = interpolate(
    frame,
    [0, TOTAL_FRAMES],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );
  const glowIntensity = speedRatio * 0.6;

  return (
    <div
      style={{
        position: 'absolute',
        left: MOLD_CENTER_X - MOLD_HALF_WIDTH - MOLD_GAP_OPEN,
        top: MOLD_CENTER_Y - MOLD_HALF_HEIGHT / 2 - 40,
        width: (MOLD_HALF_WIDTH + MOLD_GAP_OPEN) * 2,
        height: MOLD_HALF_HEIGHT + 300,
      }}
    >
      {/* Background glow */}
      <div
        style={{
          position: 'absolute',
          left: '50%',
          top: '40%',
          transform: 'translate(-50%, -50%)',
          width: 400,
          height: 400,
          borderRadius: '50%',
          background: `radial-gradient(circle, rgba(217,148,74,${glowIntensity}) 0%, transparent 70%)`,
          pointerEvents: 'none',
        }}
      />

      {/* Left mold half */}
      <div
        style={{
          position: 'absolute',
          left: MOLD_GAP_OPEN - moldGap / 2 - MOLD_HALF_WIDTH / 2,
          top: 40,
          width: MOLD_HALF_WIDTH / 2,
          height: MOLD_HALF_HEIGHT,
          background: `linear-gradient(90deg, ${MOLD_COLOR}, #90A4AE)`,
          borderRadius: '8px 0 0 8px',
          boxShadow: `inset -4px 0 12px rgba(0,0,0,0.4), 2px 0 8px rgba(0,0,0,0.3)`,
        }}
      >
        {/* Cavity detail */}
        <div
          style={{
            position: 'absolute',
            right: 0,
            top: MOLD_HALF_HEIGHT / 2 - PART_HEIGHT / 2,
            width: PART_WIDTH / 2,
            height: PART_HEIGHT,
            background: '#546E7A',
            borderRadius: '4px 0 0 4px',
          }}
        />
      </div>

      {/* Right mold half */}
      <div
        style={{
          position: 'absolute',
          left: MOLD_GAP_OPEN + moldGap / 2,
          top: 40,
          width: MOLD_HALF_WIDTH / 2,
          height: MOLD_HALF_HEIGHT,
          background: `linear-gradient(270deg, ${MOLD_COLOR}, #90A4AE)`,
          borderRadius: '0 8px 8px 0',
          boxShadow: `inset 4px 0 12px rgba(0,0,0,0.4), -2px 0 8px rgba(0,0,0,0.3)`,
        }}
      >
        {/* Cavity detail */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            top: MOLD_HALF_HEIGHT / 2 - PART_HEIGHT / 2,
            width: PART_WIDTH / 2,
            height: PART_HEIGHT,
            background: '#546E7A',
            borderRadius: '0 4px 4px 0',
          }}
        />
      </div>

      {/* Forming part (visible during injection) */}
      {showForming && (
        <div
          style={{
            position: 'absolute',
            left: MOLD_GAP_OPEN - PART_WIDTH / 2,
            top: 40 + MOLD_HALF_HEIGHT / 2 - PART_HEIGHT / 2,
            width: PART_WIDTH,
            height: PART_HEIGHT,
            background: PART_COLOR,
            borderRadius: 6,
            opacity: formingOpacity,
            boxShadow: `0 0 12px rgba(217,148,74,${formingOpacity * 0.5})`,
          }}
        />
      )}

      {/* Ejecting part */}
      {partVisible && (
        <div
          style={{
            position: 'absolute',
            left: MOLD_GAP_OPEN - PART_WIDTH / 2,
            top: 40 + MOLD_HALF_HEIGHT / 2 - PART_HEIGHT / 2 - partEjectY,
            width: PART_WIDTH,
            height: PART_HEIGHT,
            background: PART_COLOR,
            borderRadius: 6,
            opacity: partOpacity,
            boxShadow: `0 0 16px rgba(217,148,74,0.6)`,
          }}
        />
      )}

      {/* Speed lines (visible at high speed) */}
      {speedRatio > 0.4 && (
        <>
          {[...Array(Math.floor(speedRatio * 6))].map((_, i) => (
            <div
              key={i}
              style={{
                position: 'absolute',
                left: MOLD_GAP_OPEN - 1,
                top: 40 + MOLD_HALF_HEIGHT / 2 - 100 - i * 30,
                width: 2,
                height: 20,
                background: `rgba(217,148,74,${speedRatio * 0.4})`,
                borderRadius: 1,
              }}
            />
          ))}
        </>
      )}
    </div>
  );
};

export default MoldCycleAnimation;
