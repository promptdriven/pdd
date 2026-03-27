import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  Easing,
  interpolate,
  Sequence,
  staticFile,
  OffthreadVideo,
} from 'remotion';

// ---------------------------------------------------------------------------
// Sub-components (each in their own file for maintainability)
// ---------------------------------------------------------------------------
import { MoldCycleAnimation } from './MoldCycleAnimation';
import { ExponentialCounter } from './ExponentialCounter';
import { ProgressBar } from './ProgressBar';
import { EjectedPartsStream } from './EjectedPartsStream';

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------
import {
  BG_COLOR,
  COUNTER_TEXT_COLOR,
  LABEL_TEXT_COLOR,
  LABEL_OPACITY,
  PROGRESS_TRACK_COLOR,
  PROGRESS_FILL_START,
  PROGRESS_FILL_END,
  COUNTER_START,
  COUNTER_END,
  COUNTER_X,
  COUNTER_Y,
  COUNTER_FONT_SIZE,
  PROGRESS_BAR_WIDTH,
  PROGRESS_BAR_HEIGHT,
  PROGRESS_BAR_X,
  PROGRESS_BAR_Y,
  TOTAL_FRAMES,
} from './constants';

// ---------------------------------------------------------------------------
// Default props
// ---------------------------------------------------------------------------
export const defaultPart2ParadigmShift04MoldProductionCounterProps = {};

// ---------------------------------------------------------------------------
// Main Component
// ---------------------------------------------------------------------------
export const Part2ParadigmShift04MoldProductionCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Overall scene fade-in (quick, from frame 0)
  const sceneOpacity = interpolate(frame, [0, 8], [0.7, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Subtle background video overlay opacity
  const videoOpacity = interpolate(frame, [0, 20], [0, 0.35], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Title fade
  const titleOpacity = interpolate(frame, [0, 15, 240, 270], [1, 1, 1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Vignette overlay for cinematic feel
  const vignetteStyle: React.CSSProperties = {
    position: 'absolute',
    top: 0,
    left: 0,
    width: '100%',
    height: '100%',
    background:
      'radial-gradient(ellipse at center, transparent 50%, rgba(0,0,0,0.5) 100%)',
    pointerEvents: 'none',
  };

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: sceneOpacity,
      }}
    >
      {/* Background video layer — mold producing parts */}
      <AbsoluteFill style={{ opacity: videoOpacity }}>
        <OffthreadVideo
          src={staticFile('veo/mold_producing_parts.mp4')}
          style={{
            width: '100%',
            height: '100%',
            objectFit: 'cover',
          }}
          muted
        />
      </AbsoluteFill>

      {/* Dark overlay on video for contrast */}
      <AbsoluteFill
        style={{
          backgroundColor: 'rgba(10,15,26,0.65)',
        }}
      />

      {/* Vignette */}
      <div style={vignetteStyle} />

      {/* Grid/scan lines for industrial feel */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          backgroundImage:
            'repeating-linear-gradient(0deg, transparent, transparent 3px, rgba(255,255,255,0.015) 3px, rgba(255,255,255,0.015) 4px)',
          pointerEvents: 'none',
        }}
      />

      {/* Title: "Mold Production" */}
      <div
        style={{
          position: 'absolute',
          left: 80,
          top: 60,
          opacity: titleOpacity,
        }}
      >
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 18,
            fontWeight: 500,
            color: '#4A90D9',
            letterSpacing: '0.15em',
            textTransform: 'uppercase',
            marginBottom: 8,
            opacity: 0.9,
          }}
        >
          Injection Molding
        </div>
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 36,
            fontWeight: 700,
            color: COUNTER_TEXT_COLOR,
            letterSpacing: '-0.01em',
          }}
        >
          Production Scale
        </div>
        {/* Divider line */}
        <div
          style={{
            width: 60,
            height: 3,
            background: 'linear-gradient(90deg, #4A90D9, #5AAA6E)',
            borderRadius: 2,
            marginTop: 14,
            opacity: 0.85,
          }}
        />
      </div>

      {/* Mold cycle 2D animation (left-center area) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <MoldCycleAnimation />
      </Sequence>

      {/* Ejected parts visual stream */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <EjectedPartsStream />
      </Sequence>

      {/* Counter (lower-right) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ExponentialCounter
          start={COUNTER_START}
          end={COUNTER_END}
          fontSize={COUNTER_FONT_SIZE}
          color={COUNTER_TEXT_COLOR}
          labelColor={LABEL_TEXT_COLOR}
          labelOpacity={LABEL_OPACITY}
          x={COUNTER_X}
          y={COUNTER_Y}
          totalFrames={TOTAL_FRAMES}
        />
      </Sequence>

      {/* Progress bar (beneath counter) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ProgressBar
          barWidth={PROGRESS_BAR_WIDTH}
          barHeight={PROGRESS_BAR_HEIGHT}
          x={PROGRESS_BAR_X}
          y={PROGRESS_BAR_Y}
          trackColor={PROGRESS_TRACK_COLOR}
          fillStartColor={PROGRESS_FILL_START}
          fillEndColor={PROGRESS_FILL_END}
          totalFrames={TOTAL_FRAMES}
        />
      </Sequence>

      {/* Milestone flash overlays */}
      <MilestoneFlash />
    </AbsoluteFill>
  );
};

// ---------------------------------------------------------------------------
// MilestoneFlash — brief screen flash when counter hits milestones
// ---------------------------------------------------------------------------
const MilestoneFlash: React.FC = () => {
  const frame = useCurrentFrame();

  // Approximate milestone frames (based on easeIn(exp) curve for counter)
  // These are approximations since the exact frames depend on exp easing
  const milestoneFrames = [
    { value: 10, approxFrame: 180 },
    { value: 100, approxFrame: 220 },
    { value: 1000, approxFrame: 260 },
    { value: 10000, approxFrame: 295 },
  ];

  let flashOpacity = 0;
  for (const m of milestoneFrames) {
    const dist = frame - m.approxFrame;
    if (dist >= 0 && dist < 8) {
      const t = dist / 8;
      flashOpacity = Math.max(flashOpacity, (1 - t) * 0.1);
    }
  }

  if (flashOpacity <= 0) return null;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: `rgba(74,144,217,${flashOpacity})`,
        pointerEvents: 'none',
      }}
    />
  );
};

export default Part2ParadigmShift04MoldProductionCounter;
