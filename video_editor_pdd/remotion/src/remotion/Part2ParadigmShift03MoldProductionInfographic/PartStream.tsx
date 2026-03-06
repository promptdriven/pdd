import React, { useMemo } from "react";
import { useCurrentFrame, interpolate, spring } from "remotion";
import {
  CONVEYOR_X_START,
  CONVEYOR_X_END,
  PART_W,
  PART_H,
  PART_FILL,
  PART_BORDER,
  PART_Y,
  NORMAL_INTERVAL,
  FAST_INTERVAL,
  PART_TRAVEL_FRAMES,
  STREAM_START,
  STREAM_FAST_START,
  STREAM_PAUSE,
  DEFECT_APPEAR,
  DEFECT_DISSOLVE_START,
  DEFECT_DISSOLVE_END,
  CORRECTED_STREAM_START,
  FADEOUT_START,
  FADEOUT_END,
  DEFECT_COLOR,
  FPS,
} from "./constants";

interface PartInfo {
  id: number;
  spawnFrame: number;
  isDefect: boolean;
}

/**
 * Computes the list of parts that should spawn during the animation.
 * The last part before the stream pause is marked as defective.
 */
function computeParts(): PartInfo[] {
  const parts: PartInfo[] = [];
  let id = 0;
  let f = STREAM_START;

  // Phase 1: normal interval (frames 40-180)
  while (f < STREAM_FAST_START) {
    parts.push({ id: id++, spawnFrame: f, isDefect: false });
    f += NORMAL_INTERVAL;
  }

  // Phase 2: fast interval (frames 180-240)
  while (f < STREAM_PAUSE) {
    parts.push({ id: id++, spawnFrame: f, isDefect: false });
    f += FAST_INTERVAL;
  }

  // Mark the last part before pause as the defective one
  if (parts.length > 0) {
    parts[parts.length - 1].isDefect = true;
  }

  // Phase 3: corrected stream (frames 360-570)
  f = CORRECTED_STREAM_START;
  while (f < FADEOUT_START) {
    parts.push({ id: id++, spawnFrame: f, isDefect: false });
    f += NORMAL_INTERVAL;
  }

  return parts;
}

// Pre-compute parts list (module-level, deterministic)
const ALL_PARTS = computeParts();
const DEFECT_PART = ALL_PARTS.find((p) => p.isDefect);

/**
 * Returns the X position of the defect part at a given frame.
 */
export function getDefectPartX(frame: number): number {
  if (!DEFECT_PART) return CONVEYOR_X_START + 200;
  const localFrame = Math.max(0, frame - DEFECT_PART.spawnFrame);
  return interpolate(
    localFrame,
    [0, PART_TRAVEL_FRAMES],
    [CONVEYOR_X_START, CONVEYOR_X_END],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
}

interface SinglePartProps {
  part: PartInfo;
  globalFrame: number;
}

const SinglePart: React.FC<SinglePartProps> = ({ part, globalFrame }) => {
  const localFrame = globalFrame - part.spawnFrame;
  if (localFrame < 0) return null;

  // Spring pop-in
  const popScale = spring({
    frame: localFrame,
    fps: FPS,
    config: { damping: 14, stiffness: 220 },
  });

  // Part moves from mold exit to conveyor end
  const x = interpolate(
    localFrame,
    [0, PART_TRAVEL_FRAMES],
    [CONVEYOR_X_START, CONVEYOR_X_END],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Fade out at global fadeout
  const fadeOut = interpolate(
    globalFrame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Defect handling
  let fill = PART_FILL;
  let stroke = PART_BORDER;
  let partOpacity = fadeOut;
  let partScale = popScale;

  if (part.isDefect) {
    // Red flash after defect appear frame
    const defectLocalFrame = globalFrame - DEFECT_APPEAR;
    if (defectLocalFrame >= 0) {
      const flash = interpolate(
        Math.sin(defectLocalFrame * 0.3),
        [-1, 1],
        [0.5, 1.0]
      );
      fill = DEFECT_COLOR;
      stroke = DEFECT_COLOR;
      partOpacity = fadeOut * flash;
    }

    // Dissolve at fix time
    if (globalFrame >= DEFECT_DISSOLVE_START) {
      const dissolve = interpolate(
        globalFrame,
        [DEFECT_DISSOLVE_START, DEFECT_DISSOLVE_END],
        [1, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      );
      const shrink = interpolate(
        globalFrame,
        [DEFECT_DISSOLVE_START, DEFECT_DISSOLVE_END],
        [1, 0.5],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      );
      partOpacity = dissolve;
      partScale = shrink;
    }
  }

  if (partOpacity <= 0) return null;

  const cx = x;
  const cy = PART_Y + PART_H / 2;

  return (
    <g
      transform={`translate(${cx}, ${cy}) scale(${partScale}) translate(${-cx}, ${-cy})`}
      opacity={partOpacity}
    >
      <rect
        x={x - PART_W / 2}
        y={PART_Y}
        width={PART_W}
        height={PART_H}
        rx={8}
        ry={8}
        fill={fill}
        stroke={stroke}
        strokeWidth={1.5}
      />
    </g>
  );
};

export const PartStream: React.FC = () => {
  const frame = useCurrentFrame();
  const parts = useMemo(() => ALL_PARTS, []);

  // Only render parts that have spawned
  const activeParts = parts.filter((p) => frame >= p.spawnFrame);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {activeParts.map((part) => (
        <SinglePart key={part.id} part={part} globalFrame={frame} />
      ))}
    </svg>
  );
};

export default PartStream;
