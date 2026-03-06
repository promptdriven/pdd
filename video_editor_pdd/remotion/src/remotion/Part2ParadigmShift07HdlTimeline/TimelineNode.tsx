import React from "react";
import {
  useCurrentFrame,
  spring,
  interpolate,
  Easing,
} from "remotion";
import {
  NODE_CIRCLE_SIZE,
  NODE_ICON_SIZE,
  NODE_BORDER_WIDTH,
  NODE_FILL,
  DESCRIPTOR_COLOR,
  SPRING_CONFIG,
  PULSE_DURATION,
  FPS,
} from "./constants";

type IconType = "pencil" | "code_brackets" | "chip";

interface TimelineNodeProps {
  x: number;
  y: number;
  icon: IconType;
  year: string;
  descriptor: string;
  color: string;
  activateFrame: number;
  dimOpacity: number;
  globalOpacity: number;
}

const PencilIcon: React.FC<{ size: number; color: string }> = ({
  size,
  color,
}) => (
  <svg width={size} height={size} viewBox="0 0 40 40" fill="none">
    <path
      d="M28.5 6.5L33.5 11.5L12.5 32.5L5 35L7.5 27.5L28.5 6.5Z"
      stroke={color}
      strokeWidth={2.5}
      strokeLinecap="round"
      strokeLinejoin="round"
    />
    <path
      d="M25 10L30 15"
      stroke={color}
      strokeWidth={2.5}
      strokeLinecap="round"
    />
    <path
      d="M7.5 27.5L12.5 32.5"
      stroke={color}
      strokeWidth={2}
      strokeLinecap="round"
    />
  </svg>
);

const CodeBracketsIcon: React.FC<{ size: number; color: string }> = ({
  size,
  color,
}) => (
  <svg width={size} height={size} viewBox="0 0 40 40" fill="none">
    <path
      d="M14 8L6 20L14 32"
      stroke={color}
      strokeWidth={2.5}
      strokeLinecap="round"
      strokeLinejoin="round"
    />
    <path
      d="M26 8L34 20L26 32"
      stroke={color}
      strokeWidth={2.5}
      strokeLinecap="round"
      strokeLinejoin="round"
    />
  </svg>
);

const ChipIcon: React.FC<{ size: number; color: string }> = ({
  size,
  color,
}) => (
  <svg width={size} height={size} viewBox="0 0 40 40" fill="none">
    <rect
      x="10"
      y="10"
      width="20"
      height="20"
      rx="2"
      stroke={color}
      strokeWidth={2.5}
    />
    <rect x="15" y="15" width="10" height="10" rx="1" fill={color} opacity={0.3} />
    {/* Top pins */}
    <line x1="16" y1="5" x2="16" y2="10" stroke={color} strokeWidth={2} />
    <line x1="24" y1="5" x2="24" y2="10" stroke={color} strokeWidth={2} />
    {/* Bottom pins */}
    <line x1="16" y1="30" x2="16" y2="35" stroke={color} strokeWidth={2} />
    <line x1="24" y1="30" x2="24" y2="35" stroke={color} strokeWidth={2} />
    {/* Left pins */}
    <line x1="5" y1="16" x2="10" y2="16" stroke={color} strokeWidth={2} />
    <line x1="5" y1="24" x2="10" y2="24" stroke={color} strokeWidth={2} />
    {/* Right pins */}
    <line x1="30" y1="16" x2="35" y2="16" stroke={color} strokeWidth={2} />
    <line x1="30" y1="24" x2="35" y2="24" stroke={color} strokeWidth={2} />
  </svg>
);

const ICON_MAP: Record<IconType, React.FC<{ size: number; color: string }>> = {
  pencil: PencilIcon,
  code_brackets: CodeBracketsIcon,
  chip: ChipIcon,
};

export const TimelineNode: React.FC<TimelineNodeProps> = ({
  x,
  y,
  icon,
  year,
  descriptor,
  color,
  activateFrame,
  dimOpacity,
  globalOpacity,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - activateFrame;

  if (localFrame < 0) return null;

  const scaleVal = spring({
    frame: localFrame,
    fps: FPS,
    config: SPRING_CONFIG,
  });

  const iconOpacity = interpolate(localFrame, [0, 15], [0, 1], {
    extrapolateRight: "clamp",
  });

  // Radial pulse
  const pulseProgress = interpolate(
    localFrame,
    [0, PULSE_DURATION],
    [0, 1],
    { extrapolateRight: "clamp" }
  );
  const pulseScale = interpolate(pulseProgress, [0, 1], [1, 2]);
  const pulseOpacity = interpolate(pulseProgress, [0, 1], [0.6, 0], {
    easing: Easing.out(Easing.quad),
  });

  const IconComponent = ICON_MAP[icon];

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        transform: "translate(-50%, -50%)",
        opacity: dimOpacity * globalOpacity,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
      }}
    >
      {/* Year label above */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 700,
          fontSize: 22,
          color,
          marginBottom: 12,
          opacity: iconOpacity,
        }}
      >
        {year}
      </div>

      {/* Node circle with icon */}
      <div
        style={{
          position: "relative",
          width: NODE_CIRCLE_SIZE,
          height: NODE_CIRCLE_SIZE,
        }}
      >
        {/* Radial pulse */}
        {pulseProgress < 1 && (
          <div
            style={{
              position: "absolute",
              left: "50%",
              top: "50%",
              width: NODE_CIRCLE_SIZE,
              height: NODE_CIRCLE_SIZE,
              borderRadius: "50%",
              border: `2px solid ${color}`,
              transform: `translate(-50%, -50%) scale(${pulseScale})`,
              opacity: pulseOpacity,
              pointerEvents: "none",
            }}
          />
        )}

        {/* Circle */}
        <div
          style={{
            width: NODE_CIRCLE_SIZE,
            height: NODE_CIRCLE_SIZE,
            borderRadius: "50%",
            backgroundColor: NODE_FILL,
            border: `${NODE_BORDER_WIDTH}px solid ${color}`,
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            transform: `scale(${scaleVal})`,
          }}
        >
          <div style={{ opacity: iconOpacity }}>
            <IconComponent size={NODE_ICON_SIZE} color={color} />
          </div>
        </div>
      </div>

      {/* Descriptor below */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontWeight: 500,
          fontSize: 16,
          color: DESCRIPTOR_COLOR,
          marginTop: 12,
          opacity: iconOpacity,
          whiteSpace: "nowrap",
        }}
      >
        {descriptor}
      </div>
    </div>
  );
};

export default TimelineNode;
