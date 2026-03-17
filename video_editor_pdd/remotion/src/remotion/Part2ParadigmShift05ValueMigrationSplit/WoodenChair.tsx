import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CHAIR_CENTER_X,
  CHAIR_CENTER_Y,
  CHAIR_WIDTH,
  CHAIR_HEIGHT,
  WOOD_BODY,
  WOOD_GRAIN,
  CHISEL_COLOR,
  CHAIR_DRAW_START,
  CHAIR_DRAW_END,
  CHISEL_MARK_START,
  CHISEL_MARK_STAGGER,
  CHISEL_MARK_COUNT,
} from "./constants";

export const WoodenChair: React.FC = () => {
  const frame = useCurrentFrame();

  // Chair outline draw progress (0 to 1)
  const drawProgress = interpolate(
    frame,
    [CHAIR_DRAW_START, CHAIR_DRAW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // SVG path total length for stroke-dasharray animation
  const chairPathLength = 1400;
  const visibleLength = drawProgress * chairPathLength;

  // Chisel marks
  const chiselMarks: Array<{ x1: number; y1: number; x2: number; y2: number }> = [];
  for (let i = 0; i < CHISEL_MARK_COUNT; i++) {
    const angle = (i * 37 + 15) % 360;
    const rad = (angle * Math.PI) / 180;
    const dist = 40 + (i * 17) % 80;
    const cx = CHAIR_CENTER_X + Math.cos(rad) * dist;
    const cy = CHAIR_CENTER_Y - 30 + Math.sin(rad) * dist;
    chiselMarks.push({
      x1: cx - 4,
      y1: cy - 3,
      x2: cx + 4,
      y2: cy + 3,
    });
  }

  return (
    <svg
      width={LEFT_PANEL_WIDTH}
      height={1080}
      viewBox={`0 0 ${LEFT_PANEL_WIDTH} 1080`}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Chair body — simplified side-view chair */}
      <g
        strokeDasharray={chairPathLength}
        strokeDashoffset={chairPathLength - visibleLength}
      >
        {/* Seat */}
        <rect
          x={CHAIR_CENTER_X - CHAIR_WIDTH / 2}
          y={CHAIR_CENTER_Y - 20}
          width={CHAIR_WIDTH}
          height={30}
          rx={6}
          fill={WOOD_BODY}
          fillOpacity={drawProgress * 0.8}
          stroke={WOOD_BODY}
          strokeWidth={2}
          strokeOpacity={drawProgress}
        />
        {/* Backrest */}
        <rect
          x={CHAIR_CENTER_X - CHAIR_WIDTH / 2 + 20}
          y={CHAIR_CENTER_Y - CHAIR_HEIGHT / 2 + 40}
          width={CHAIR_WIDTH - 40}
          height={CHAIR_HEIGHT / 2 - 60}
          rx={8}
          fill={WOOD_BODY}
          fillOpacity={drawProgress * 0.7}
          stroke={WOOD_BODY}
          strokeWidth={2}
          strokeOpacity={drawProgress}
        />
        {/* Left back leg */}
        <rect
          x={CHAIR_CENTER_X - CHAIR_WIDTH / 2 + 20}
          y={CHAIR_CENTER_Y - CHAIR_HEIGHT / 2 + 40}
          width={16}
          height={CHAIR_HEIGHT - 80}
          rx={4}
          fill={WOOD_BODY}
          fillOpacity={drawProgress * 0.85}
          stroke={WOOD_BODY}
          strokeWidth={1.5}
          strokeOpacity={drawProgress}
        />
        {/* Right back leg */}
        <rect
          x={CHAIR_CENTER_X + CHAIR_WIDTH / 2 - 36}
          y={CHAIR_CENTER_Y - CHAIR_HEIGHT / 2 + 40}
          width={16}
          height={CHAIR_HEIGHT - 80}
          rx={4}
          fill={WOOD_BODY}
          fillOpacity={drawProgress * 0.85}
          stroke={WOOD_BODY}
          strokeWidth={1.5}
          strokeOpacity={drawProgress}
        />
        {/* Left front leg */}
        <rect
          x={CHAIR_CENTER_X - CHAIR_WIDTH / 2 + 20}
          y={CHAIR_CENTER_Y + 10}
          width={16}
          height={CHAIR_HEIGHT / 2 - 50}
          rx={4}
          fill={WOOD_BODY}
          fillOpacity={drawProgress * 0.85}
          stroke={WOOD_BODY}
          strokeWidth={1.5}
          strokeOpacity={drawProgress}
        />
        {/* Right front leg */}
        <rect
          x={CHAIR_CENTER_X + CHAIR_WIDTH / 2 - 36}
          y={CHAIR_CENTER_Y + 10}
          width={16}
          height={CHAIR_HEIGHT / 2 - 50}
          rx={4}
          fill={WOOD_BODY}
          fillOpacity={drawProgress * 0.85}
          stroke={WOOD_BODY}
          strokeWidth={1.5}
          strokeOpacity={drawProgress}
        />
        {/* Cross brace */}
        <rect
          x={CHAIR_CENTER_X - CHAIR_WIDTH / 2 + 36}
          y={CHAIR_CENTER_Y + CHAIR_HEIGHT / 4}
          width={CHAIR_WIDTH - 72}
          height={8}
          rx={3}
          fill={WOOD_BODY}
          fillOpacity={drawProgress * 0.6}
          stroke={WOOD_BODY}
          strokeWidth={1}
          strokeOpacity={drawProgress * 0.8}
        />
      </g>

      {/* Wood grain texture lines */}
      {drawProgress > 0.5 && (
        <g opacity={0.1 * drawProgress}>
          {[0, 1, 2, 3, 4].map((i) => (
            <line
              key={`grain-${i}`}
              x1={CHAIR_CENTER_X - 80 + i * 40}
              y1={CHAIR_CENTER_Y - 15}
              x2={CHAIR_CENTER_X - 80 + i * 40 + 10}
              y2={CHAIR_CENTER_Y + 5}
              stroke={WOOD_GRAIN}
              strokeWidth={1}
              strokeOpacity={0.3}
            />
          ))}
        </g>
      )}

      {/* Chisel marks accumulating */}
      {chiselMarks.map((mark, i) => {
        const markFrame = CHISEL_MARK_START + i * CHISEL_MARK_STAGGER;
        const markOpacity = interpolate(
          frame,
          [markFrame, markFrame + 5],
          [0, 0.3],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
        );
        return (
          <line
            key={`chisel-${i}`}
            x1={mark.x1}
            y1={mark.y1}
            x2={mark.x2}
            y2={mark.y2}
            stroke={CHISEL_COLOR}
            strokeWidth={1}
            opacity={markOpacity}
          />
        );
      })}
    </svg>
  );
};

// Need this constant locally since we reference it but it's the left panel width
const LEFT_PANEL_WIDTH = 958;
