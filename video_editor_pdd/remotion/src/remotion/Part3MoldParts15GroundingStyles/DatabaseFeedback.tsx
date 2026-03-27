import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TEAM_COLOR,
  SUCCESS_GREEN,
  DB_ICON_X,
  DB_ICON_Y,
  DB_ICON_WIDTH,
  DB_ICON_HEIGHT,
} from "./constants";

// ─── Flow Arrow (solid) ───
interface FlowArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  startFrame: number;
  durationFrames: number;
  label: string;
}

export const FlowArrow: React.FC<FlowArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  startFrame,
  durationFrames,
  label,
}) => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - startFrame);

  const progress = interpolate(localFrame, [0, durationFrames], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  const opacity = interpolate(localFrame, [0, 10], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Interpolated endpoint
  const currentX = fromX + (toX - fromX) * progress;
  const currentY = fromY + (toY - fromY) * progress;

  // Label travels along the arrow
  const labelProgress = interpolate(
    localFrame,
    [10, durationFrames - 5],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );
  const labelX = fromX + (toX - fromX) * labelProgress;
  const labelY = fromY + (toY - fromY) * labelProgress - 18;

  return (
    <svg
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        pointerEvents: "none",
        opacity,
      }}
    >
      {/* Arrow line */}
      <line
        x1={fromX}
        y1={fromY}
        x2={currentX}
        y2={currentY}
        stroke={TEAM_COLOR}
        strokeWidth={2.5}
        opacity={0.5}
      />
      {/* Arrow head */}
      {progress > 0.1 && (
        <polygon
          points={`${currentX},${currentY} ${currentX - 8},${currentY - 12} ${currentX + 8},${currentY - 12}`}
          fill={TEAM_COLOR}
          opacity={0.6}
        />
      )}
      {/* Traveling label */}
      {localFrame > 10 && (
        <text
          x={labelX}
          y={labelY}
          textAnchor="middle"
          fontFamily="'JetBrains Mono', monospace"
          fontSize={11}
          fill={SUCCESS_GREEN}
          opacity={interpolate(
            localFrame,
            [10, 20, durationFrames - 10, durationFrames],
            [0, 0.9, 0.9, 0.5],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          )}
        >
          {label}
        </text>
      )}
    </svg>
  );
};

// ─── Dashed Arrow ───
interface DashedArrowProps {
  fromX: number;
  fromY: number;
  toX: number;
  toY: number;
  startFrame: number;
  label: string;
}

export const DashedArrow: React.FC<DashedArrowProps> = ({
  fromX,
  fromY,
  toX,
  toY,
  startFrame,
  label,
}) => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - startFrame);

  const opacity = interpolate(localFrame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Dash animation offset
  const dashOffset = localFrame * 1.5;

  return (
    <svg
      style={{
        position: "absolute",
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        pointerEvents: "none",
        opacity: opacity * 0.4,
      }}
    >
      <line
        x1={fromX}
        y1={fromY}
        x2={toX}
        y2={toY}
        stroke={TEAM_COLOR}
        strokeWidth={2}
        strokeDasharray="8 6"
        strokeDashoffset={-dashOffset}
      />
      {/* Arrow head */}
      <polygon
        points={`${toX},${toY} ${toX - 6},${toY - 10} ${toX + 6},${toY - 10}`}
        fill={TEAM_COLOR}
        opacity={0.5}
      />
      {/* Label */}
      <text
        x={toX}
        y={toY + 22}
        textAnchor="middle"
        fontFamily="Inter, sans-serif"
        fontSize={13}
        fontWeight={600}
        fill={TEAM_COLOR}
        opacity={0.7}
      >
        {label}
      </text>
    </svg>
  );
};

// ─── Database Icon ───
interface DatabaseIconProps {
  fadeStartFrame: number;
  pulseStartFrame: number;
}

export const DatabaseIcon: React.FC<DatabaseIconProps> = ({
  fadeStartFrame,
  pulseStartFrame,
}) => {
  const frame = useCurrentFrame();

  const localFadeFrame = Math.max(0, frame - fadeStartFrame);
  const opacity = interpolate(localFadeFrame, [0, 15], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Pulse effect when data arrives
  const pulseLocal = Math.max(0, frame - pulseStartFrame);
  const pulseScale =
    pulseLocal > 0
      ? 1 +
        interpolate(pulseLocal % 30, [0, 15, 30], [0, 0.08, 0], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.inOut(Easing.sin),
        })
      : 1;

  const cx = DB_ICON_X;
  const cy = DB_ICON_Y;
  const w = DB_ICON_WIDTH;
  const h = DB_ICON_HEIGHT;

  return (
    <div
      style={{
        position: "absolute",
        left: cx - w / 2 - 60,
        top: cy - h / 2 - 20,
        width: w + 120,
        height: h + 60,
        opacity,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
      }}
    >
      <svg
        width={w + 20}
        height={h + 10}
        style={{ transform: `scale(${pulseScale})` }}
      >
        {/* Cylinder body */}
        <rect
          x={10}
          y={15}
          width={w}
          height={h - 15}
          rx={4}
          fill={TEAM_COLOR}
          fillOpacity={0.2}
          stroke={TEAM_COLOR}
          strokeWidth={2}
        />
        {/* Top ellipse */}
        <ellipse
          cx={10 + w / 2}
          cy={15}
          rx={w / 2}
          ry={10}
          fill={TEAM_COLOR}
          fillOpacity={0.3}
          stroke={TEAM_COLOR}
          strokeWidth={2}
        />
        {/* Bottom ellipse (rim) */}
        <ellipse
          cx={10 + w / 2}
          cy={h}
          rx={w / 2}
          ry={10}
          fill="none"
          stroke={TEAM_COLOR}
          strokeWidth={2}
        />
        {/* Inner lines for disk detail */}
        <ellipse
          cx={10 + w / 2}
          cy={30}
          rx={w / 2 - 2}
          ry={6}
          fill="none"
          stroke={TEAM_COLOR}
          strokeWidth={1}
          opacity={0.3}
        />
      </svg>
      {/* Label */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 600,
          color: TEAM_COLOR,
          marginTop: 6,
          textAlign: "center",
          whiteSpace: "nowrap",
        }}
      >
        Grounding Database
      </div>
    </div>
  );
};

// ─── Terminal Note ───
interface TerminalNoteProps {
  startFrame: number;
}

export const TerminalNote: React.FC<TerminalNoteProps> = ({ startFrame }) => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - startFrame);

  const opacity = interpolate(localFrame, [0, 20], [0, 0.85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        left: DB_ICON_X - 140,
        top: DB_ICON_Y + 65,
        opacity,
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: 11,
        color: SUCCESS_GREEN,
        textAlign: "center",
        width: 280,
      }}
    >
      pdd fix → (prompt, code) → cloud
    </div>
  );
};
