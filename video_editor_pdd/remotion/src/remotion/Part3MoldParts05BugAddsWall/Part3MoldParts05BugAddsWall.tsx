import React from 'react';
import { AbsoluteFill, Sequence, useCurrentFrame, interpolate } from 'remotion';
import {
  BG_COLOR,
  TOTAL_FRAMES,
  LIQUID_DRAIN_START,
  LIQUID_FILL_START,
  WALL_SLIDE_START,
  CAVITY_X,
  CAVITY_Y,
  CAVITY_WIDTH,
  CAVITY_HEIGHT,
  LIQUID_FROM,
  LIQUID_TO,
  EXISTING_WALLS,
} from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { MoldCrossSection } from './MoldCrossSection';
import { BugPulse } from './BugPulse';
import { TerminalWindow } from './TerminalWindow';
import { NewWall } from './NewWall';
import { LiquidFlow, LiquidDrain } from './LiquidFlow';

export const defaultPart3MoldParts05BugAddsWallProps = {};

/**
 * Section 3.5 — Bug Found: Add a Wall
 *
 * 480 frames @ 30fps = 16 seconds
 *
 * Sequence:
 *   0–30    Bug discovery (red pulse radiates in the mold cavity)
 *  30–60    Hold on bug, terminal appears with "pdd bug user_parser"
 *  60–120   "BUG" fades out, new wall slides in from right
 * 120–150   Wall arrives, glow pulse, label "rejects negative IDs" fades in
 * 150–180   Hold — wall is now part of the mold
 * 180–200   Liquid drains (top-to-bottom fade out)
 * 210–250   New liquid injects from nozzle, fills cavity including new wall
 * 300       Terminal shows "All tests passing ✓"
 * 360–480   Hold final state, terminal fades slightly
 */
export const Part3MoldParts05BugAddsWall: React.FC = () => {
  const frame = useCurrentFrame();

  // The pre-existing liquid is visible from frame 0 until drain starts
  const preLiquidOpacity = interpolate(
    frame,
    [0, LIQUID_DRAIN_START],
    [0.85, 0.85],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Show pre-existing liquid only before drain phase
  const showPreLiquid = frame < LIQUID_DRAIN_START;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Mold cross-section (outer walls, cavity, nozzle, existing internal walls) */}
      <MoldCrossSection wallsOpacity={0.5} />

      {/* Pre-existing liquid in the cavity (before drain) */}
      {showPreLiquid && (
        <div
          style={{
            position: 'absolute',
            left: CAVITY_X,
            top: CAVITY_Y,
            width: CAVITY_WIDTH,
            height: CAVITY_HEIGHT,
            background: `linear-gradient(180deg, ${LIQUID_FROM}B0 0%, ${LIQUID_TO}B0 100%)`,
            borderRadius: 2,
            opacity: preLiquidOpacity,
            overflow: 'hidden',
          }}
        >
          {/* Cut-outs for existing walls */}
          {EXISTING_WALLS.map((wall, i) => (
            <div
              key={i}
              style={{
                position: 'absolute',
                left: wall.x - CAVITY_X - 2,
                top: wall.y - CAVITY_Y - 2,
                width: wall.width + 4,
                height: wall.height + 4,
                backgroundColor: '#0D1117',
                borderRadius: 3,
              }}
            />
          ))}
        </div>
      )}

      {/* Bug discovery: red pulse + "BUG" text (frames 0–90) */}
      <Sequence from={0} durationInFrames={90}>
        <BugPulse />
      </Sequence>

      {/* Terminal window appears at frame 30, persists to end */}
      <Sequence from={30} durationInFrames={TOTAL_FRAMES - 30}>
        <TerminalWindow />
      </Sequence>

      {/* New wall slides in from the right starting at frame 60 */}
      <Sequence from={WALL_SLIDE_START} durationInFrames={TOTAL_FRAMES - WALL_SLIDE_START}>
        <NewWall />
      </Sequence>

      {/* Liquid drain (frames 180–200) */}
      <Sequence from={LIQUID_DRAIN_START} durationInFrames={30}>
        <LiquidDrain />
      </Sequence>

      {/* New liquid fills (frames 210 onward), including the new wall */}
      <Sequence from={LIQUID_FILL_START} durationInFrames={TOTAL_FRAMES - LIQUID_FILL_START}>
        <LiquidFlow includeNewWall />
      </Sequence>

      {/* Insight text — appears late, reinforcing the key message */}
      <Sequence from={320} durationInFrames={160}>
        <InsightCaption />
      </Sequence>
    </AbsoluteFill>
  );
};

/** Subtle insight caption that appears in the bottom-left */
const InsightCaption: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, 20, 140, 160],
    [0, 0.85, 0.85, 0.6],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 80,
        bottom: 80,
        opacity,
        maxWidth: 500,
      }}
    >
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 22,
          fontWeight: 600,
          color: '#E2E8F0',
          lineHeight: 1.4,
          textShadow: '0 2px 12px rgba(0,0,0,0.6)',
        }}
      >
        Bugs become permanent walls,
      </div>
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 22,
          fontWeight: 600,
          color: '#E2E8F0',
          lineHeight: 1.4,
          textShadow: '0 2px 12px rgba(0,0,0,0.6)',
        }}
      >
        not temporary patches.
      </div>
      <div
        style={{
          marginTop: 8,
          width: 60,
          height: 3,
          backgroundColor: '#4A90D9',
          borderRadius: 2,
          opacity: 0.8,
        }}
      />
    </div>
  );
};

export default Part3MoldParts05BugAddsWall;
