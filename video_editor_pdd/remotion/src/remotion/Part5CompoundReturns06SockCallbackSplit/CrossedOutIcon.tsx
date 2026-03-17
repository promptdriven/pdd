import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { ICON_APPEAR_START, ICON_APPEAR_DUR } from "./constants";

/**
 * A simple crossed-out icon. Two variants:
 * - "needle": a darning needle shape with a cross-out line
 * - "patch": a patch/bandaid shape with a cross-out line
 */
export const CrossedOutIcon: React.FC<{
  variant: "needle" | "patch";
  color: string;
  opacity: number;
  x: number;
  y: number;
}> = ({ variant, color, opacity, x, y }) => {
  const frame = useCurrentFrame();

  const scale = interpolate(
    frame,
    [ICON_APPEAR_START, ICON_APPEAR_START + ICON_APPEAR_DUR],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.bezier(0.33, 1, 0.68, 1)) }
  );

  const iconOpacity = interpolate(
    frame,
    [ICON_APPEAR_START, ICON_APPEAR_START + ICON_APPEAR_DUR],
    [0, opacity],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const size = 28;

  return (
    <div
      style={{
        position: "absolute",
        left: x - size / 2,
        top: y - size / 2,
        width: size,
        height: size,
        opacity: iconOpacity,
        transform: `scale(${scale})`,
      }}
    >
      <svg width={size} height={size} viewBox="0 0 28 28">
        {variant === "needle" ? (
          /* Darning needle icon */
          <g>
            {/* Needle body */}
            <line
              x1="6"
              y1="22"
              x2="22"
              y2="6"
              stroke={color}
              strokeWidth="2"
              strokeLinecap="round"
            />
            {/* Needle eye */}
            <circle cx="21" cy="7" r="2" fill="none" stroke={color} strokeWidth="1.5" />
            {/* Thread */}
            <path
              d="M23 5 Q26 2, 24 0"
              fill="none"
              stroke={color}
              strokeWidth="1"
              strokeLinecap="round"
            />
          </g>
        ) : (
          /* Patch / bandaid icon */
          <g>
            <rect
              x="4"
              y="10"
              width="20"
              height="8"
              rx="4"
              fill="none"
              stroke={color}
              strokeWidth="1.5"
              transform="rotate(-45 14 14)"
            />
            {/* Stitch marks */}
            <circle cx="12" cy="12" r="1" fill={color} />
            <circle cx="16" cy="16" r="1" fill={color} />
            <circle cx="12" cy="16" r="1" fill={color} />
            <circle cx="16" cy="12" r="1" fill={color} />
          </g>
        )}

        {/* Cross-out line */}
        <line
          x1="3"
          y1="25"
          x2="25"
          y2="3"
          stroke={color}
          strokeWidth="2"
          strokeLinecap="round"
          opacity={0.8}
        />
      </svg>
    </div>
  );
};

export default CrossedOutIcon;
