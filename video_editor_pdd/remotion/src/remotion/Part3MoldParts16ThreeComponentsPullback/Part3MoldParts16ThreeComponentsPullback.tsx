import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  interpolate,
  useCurrentFrame,
  Easing,
} from 'remotion';
import { BlueprintGrid } from './BlueprintGrid';
import { MoldCrossSection } from './MoldCrossSection';
import { ParticleFlow } from './ParticleFlow';
import { FlowLabel } from './FlowLabel';
import { BG_COLOR, FLOW_STAGES, TOTAL_FRAMES } from './constants';

export const defaultPart3MoldParts16ThreeComponentsPullbackProps = {};

/**
 * Section 3.16: Three Components Pullback — Complete Pipeline
 *
 * Shows the full mold cross-section with continuous particle flow
 * representing: Prompt → Grounding → Tests → Code output.
 *
 * Duration: 270 frames (9s @ 30fps)
 */
export const Part3MoldParts16ThreeComponentsPullback: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Full mold cross-section — visible from frame 0, fades in over 20 frames */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <MoldCrossSection />
      </Sequence>

      {/* Particle flow — starts at frame 30 */}
      <Sequence from={30} durationInFrames={TOTAL_FRAMES - 30}>
        <ParticleFlow />
      </Sequence>

      {/* Flow labels appear staggered alongside the flow */}
      {FLOW_STAGES.map((stage, i) => (
        <Sequence
          key={stage.encodes}
          from={stage.startFrame}
          durationInFrames={TOTAL_FRAMES - stage.startFrame}
        >
          <FlowLabel
            text={stage.encodes}
            color={stage.color}
            x={stage.labelX}
            y={stage.labelY}
            componentLabel={stage.component}
          />
        </Sequence>
      ))}

      {/* Title header — fades in with the mold */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <TitleHeader />
      </Sequence>
    </AbsoluteFill>
  );
};

/**
 * Small title at top showing the pipeline concept.
 */
const TitleHeader: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, 30], [0, 0.85], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        top: 50,
        left: 0,
        right: 0,
        display: 'flex',
        justifyContent: 'center',
        opacity,
      }}
    >
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 24,
          fontWeight: 600,
          color: '#E2E8F0',
          letterSpacing: '0.05em',
          textTransform: 'uppercase',
        }}
      >
        Complete Specification Pipeline
      </div>
    </div>
  );
};

export default Part3MoldParts16ThreeComponentsPullback;
