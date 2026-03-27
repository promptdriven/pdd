import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { BG_COLOR, DURATION_FRAMES } from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { MoldCrossSection } from './MoldCrossSection';
import { BugPulse } from './BugPulse';
import { NewWall } from './NewWall';
import { TerminalWindow } from './TerminalWindow';
import { LiquidAnimation } from './LiquidAnimation';

export const defaultPart3MoldParts05BugAddsWallProps = {};

/**
 * Section 3.5: Bug Found — Add a Wall
 *
 * A bug is discovered in generated code. Instead of patching,
 * a new wall materializes in the mold. The liquid drains and
 * refills, conforming to the additional wall. Bugs become
 * permanent walls, not temporary patches.
 *
 * Duration: 480 frames (16s @ 30fps)
 */
export const Part3MoldParts05BugAddsWall: React.FC = () => {
  const frame = useCurrentFrame();

  // Subtle overall scene brightness pulse
  const scenePulse = interpolate(
    frame % 240,
    [0, 120, 240],
    [1, 1.02, 1],
    { extrapolateRight: 'clamp' }
  );

  // Narration highlight overlay — very subtle red tint during bug phase
  const bugPhaseOverlay = interpolate(
    frame,
    [0, 10, 50, 70],
    [0, 0.03, 0.03, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Mold cross-section (outer walls + existing internal walls) */}
      <MoldCrossSection wallsOpacity={0.4} />

      {/* Liquid fill / drain / refill */}
      <LiquidAnimation />

      {/* New wall slides in (on top of liquid) */}
      <NewWall />

      {/* Bug pulse and "BUG" text */}
      <BugPulse />

      {/* Terminal window */}
      <TerminalWindow />

      {/* Subtle red overlay during bug discovery */}
      {bugPhaseOverlay > 0 && (
        <AbsoluteFill
          style={{
            backgroundColor: '#EF4444',
            opacity: bugPhaseOverlay,
            pointerEvents: 'none',
          }}
        />
      )}
    </AbsoluteFill>
  );
};

export default Part3MoldParts05BugAddsWall;
