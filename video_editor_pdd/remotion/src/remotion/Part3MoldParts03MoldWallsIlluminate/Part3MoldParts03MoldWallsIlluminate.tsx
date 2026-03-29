import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import {
  BACKGROUND_COLOR,
  TOTAL_FRAMES,
  WALL_DATA,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { MoldCrossSection } from './MoldCrossSection';
import { WallLabel } from './WallLabel';

export const defaultPart3MoldParts03MoldWallsIlluminateProps = {};

/**
 * Section 3.3 — Mold walls illuminate with test constraint labels.
 *
 * 300 frames @ 30fps (10s).
 * Frames 0-30: mold zooms in, nozzle/cavity dim, walls brighten.
 * Frames 30-210: wall segments illuminate one by one with labels.
 * Frames 210-300: hold with all labels visible.
 */
export const Part3MoldParts03MoldWallsIlluminate: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Mold cross-section with zoom, dim/brighten, and wall segment glow */}
      <MoldCrossSection />

      {/* Wall labels with connectors — each in its own Sequence so
          useCurrentFrame() inside WallLabel gives the local frame.
          The label appears 5 frames after the wall segment brightens,
          giving the connector a head start in MoldCrossSection's glow. */}
      {WALL_DATA.map((wall, index) => (
        <Sequence
          key={`wall-label-${index}`}
          from={wall.frameIn + 5}
          durationInFrames={TOTAL_FRAMES - wall.frameIn - 5}
          name={`WallLabel-${wall.label}`}
        >
          <WallLabel
            text={wall.label}
            side={wall.side}
            segmentIndex={index}
          />
        </Sequence>
      ))}
    </AbsoluteFill>
  );
};

export default Part3MoldParts03MoldWallsIlluminate;
