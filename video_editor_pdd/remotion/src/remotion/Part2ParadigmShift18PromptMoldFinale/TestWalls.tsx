import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WALL_COLOR,
  CAVITY_X,
  CAVITY_Y,
  CAVITY_WIDTH,
  CAVITY_HEIGHT,
  WALL_THICKNESS,
  WALL_DRAW_DURATION,
  WALL_LABELS,
} from "./constants";

interface WallSegment {
  id: string;
  label: string;
  delayFrames: number;
  // Position & size for each wall side
  x: number;
  y: number;
  width: number;
  height: number;
  // Label position offset
  labelX: number;
  labelY: number;
  // Draw direction: "horizontal" or "vertical"
  direction: "horizontal" | "vertical";
}

const WALL_SEGMENTS: WallSegment[] = [
  {
    id: "top",
    label: WALL_LABELS[0],
    delayFrames: 0,
    x: CAVITY_X,
    y: CAVITY_Y,
    width: CAVITY_WIDTH,
    height: WALL_THICKNESS,
    labelX: CAVITY_X + CAVITY_WIDTH / 2,
    labelY: CAVITY_Y - 14,
    direction: "horizontal",
  },
  {
    id: "right",
    label: WALL_LABELS[1],
    delayFrames: 5,
    x: CAVITY_X + CAVITY_WIDTH - WALL_THICKNESS,
    y: CAVITY_Y,
    width: WALL_THICKNESS,
    height: CAVITY_HEIGHT,
    labelX: CAVITY_X + CAVITY_WIDTH + 14,
    labelY: CAVITY_Y + CAVITY_HEIGHT / 2,
    direction: "vertical",
  },
  {
    id: "bottom",
    label: WALL_LABELS[2],
    delayFrames: 10,
    x: CAVITY_X,
    y: CAVITY_Y + CAVITY_HEIGHT - WALL_THICKNESS,
    width: CAVITY_WIDTH,
    height: WALL_THICKNESS,
    labelX: CAVITY_X + CAVITY_WIDTH / 2,
    labelY: CAVITY_Y + CAVITY_HEIGHT + 18,
    direction: "horizontal",
  },
  {
    id: "left",
    label: WALL_LABELS[3],
    delayFrames: 15,
    x: CAVITY_X,
    y: CAVITY_Y,
    width: WALL_THICKNESS,
    height: CAVITY_HEIGHT,
    labelX: CAVITY_X - 14,
    labelY: CAVITY_Y + CAVITY_HEIGHT / 2,
    direction: "vertical",
  },
];

interface TestWallsProps {
  /** Frame offset from Sequence start (already handled by useCurrentFrame inside Sequence) */
  flashActive: boolean;
}

export const TestWalls: React.FC<TestWallsProps> = ({ flashActive }) => {
  const frame = useCurrentFrame();

  return (
    <>
      {WALL_SEGMENTS.map((wall) => {
        const localFrame = frame - wall.delayFrames;
        // Draw progress
        const drawProgress = interpolate(
          localFrame,
          [0, WALL_DRAW_DURATION],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.inOut(Easing.cubic),
          }
        );

        // Flash glow when code regenerates
        const flashGlow = flashActive ? 0.5 : 0;

        // Scale for draw animation
        const scaleX =
          wall.direction === "horizontal" ? drawProgress : 1;
        const scaleY =
          wall.direction === "vertical" ? drawProgress : 1;

        const wallOpacity = interpolate(drawProgress, [0, 0.1], [0, 1], {
          extrapolateRight: "clamp",
        });

        // Label fade-in after wall is drawn
        const labelOpacity = interpolate(
          localFrame,
          [WALL_DRAW_DURATION, WALL_DRAW_DURATION + 10],
          [0, 0.7],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        );

        return (
          <React.Fragment key={wall.id}>
            {/* Wall glow */}
            <div
              style={{
                position: "absolute",
                left: wall.x - 8,
                top: wall.y - 8,
                width: wall.width + 16,
                height: wall.height + 16,
                background: WALL_COLOR,
                opacity: (0.2 + flashGlow) * wallOpacity,
                filter: "blur(15px)",
                transform: `scale(${scaleX}, ${scaleY})`,
                transformOrigin:
                  wall.direction === "horizontal" ? "left center" : "center top",
              }}
            />
            {/* Wall solid */}
            <div
              style={{
                position: "absolute",
                left: wall.x,
                top: wall.y,
                width: wall.width,
                height: wall.height,
                backgroundColor: WALL_COLOR,
                opacity: wallOpacity,
                transform: `scale(${scaleX}, ${scaleY})`,
                transformOrigin:
                  wall.direction === "horizontal" ? "left center" : "center top",
                boxShadow: flashActive
                  ? `0 0 20px ${WALL_COLOR}`
                  : "none",
              }}
            />
            {/* Wall label */}
            <div
              style={{
                position: "absolute",
                left: wall.labelX,
                top: wall.labelY,
                transform: "translate(-50%, -50%)",
                fontFamily: "'JetBrains Mono', monospace",
                fontSize: 11,
                color: WALL_COLOR,
                opacity: labelOpacity,
                whiteSpace: "nowrap",
              }}
            >
              {wall.label}
            </div>
          </React.Fragment>
        );
      })}
    </>
  );
};
