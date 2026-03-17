import React from "react";
import { interpolate, Easing } from "remotion";
import { ANIM } from "./constants";

interface AbstractionIconProps {
  type: "transistor" | "schematic" | "verilog" | "hls" | "prompt";
  x: number;
  y: number;
  color: string;
  localFrame: number;
  isActive?: boolean;
  glowFrame?: number;
}

export const AbstractionIcon: React.FC<AbstractionIconProps> = ({
  type,
  x,
  y,
  color,
  localFrame,
  isActive,
  glowFrame = 0,
}) => {
  const popDelay = ANIM.ICON_POP_DELAY;
  const popDur = ANIM.ICON_POP_DURATION;

  const scale = interpolate(
    localFrame,
    [popDelay, popDelay + popDur],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.2)),
    }
  );

  const opacity = interpolate(
    localFrame,
    [popDelay, popDelay + popDur],
    [0, 0.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  if (scale <= 0) return null;

  const glowOpacity = isActive
    ? interpolate(
        glowFrame % 40,
        [0, 20, 40],
        [0.08, 0.15, 0.08],
        { extrapolateRight: "clamp", easing: Easing.inOut(Easing.sin) }
      )
    : 0;

  const iconContent = getIconSvg(type, color);
  const size = type === "prompt" ? { w: 50, h: 40 } : type === "transistor" ? { w: 30, h: 30 } : { w: 50, h: 30 };

  return (
    <div
      style={{
        position: "absolute",
        left: x + 20,
        top: y - 90,
        width: size.w,
        height: size.h,
        transform: `scale(${scale})`,
        opacity,
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
      }}
    >
      {isActive && (
        <div
          style={{
            position: "absolute",
            inset: -20,
            borderRadius: 12,
            background: `radial-gradient(circle, ${color} 0%, transparent 70%)`,
            opacity: glowOpacity,
            filter: "blur(20px)",
          }}
        />
      )}
      <svg
        width={size.w}
        height={size.h}
        viewBox={`0 0 ${size.w} ${size.h}`}
        fill="none"
      >
        {iconContent}
      </svg>
    </div>
  );
};

function getIconSvg(
  type: string,
  color: string
): React.ReactNode {
  switch (type) {
    case "transistor":
      // BJT transistor symbol
      return (
        <g stroke={color} strokeWidth={1.5} fill="none">
          <line x1={15} y1={5} x2={15} y2={25} />
          <line x1={15} y1={10} x2={25} y2={5} />
          <line x1={15} y1={20} x2={25} y2={25} />
          <line x1={5} y1={15} x2={15} y2={15} />
          <circle cx={15} cy={15} r={12} strokeWidth={1} opacity={0.3} />
        </g>
      );
    case "schematic":
      // Logic gates connected
      return (
        <g stroke={color} strokeWidth={1.2} fill="none">
          <rect x={5} y={5} width={12} height={8} rx={1} />
          <rect x={5} y={17} width={12} height={8} rx={1} />
          <rect x={28} y={10} width={14} height={10} rx={2} />
          <line x1={17} y1={9} x2={28} y2={13} />
          <line x1={17} y1={21} x2={28} y2={17} />
          <line x1={42} y1={15} x2={48} y2={15} />
        </g>
      );
    case "verilog":
      // Code block with "always @"
      return (
        <g fill={color} opacity={0.8}>
          <text x={2} y={12} fontSize={7} fontFamily="monospace">
            always @
          </text>
          <text x={6} y={22} fontSize={6} fontFamily="monospace">
            begin
          </text>
          <rect x={2} y={25} width={30} height={1} opacity={0.3} />
        </g>
      );
    case "hls":
      // High-level code block
      return (
        <g fill={color} opacity={0.8}>
          <text x={2} y={12} fontSize={7} fontFamily="monospace">
            void fn()
          </text>
          <text x={4} y={22} fontSize={6} fontFamily="monospace">
            {"{ ... }"}
          </text>
          <rect x={2} y={25} width={35} height={1} opacity={0.3} />
        </g>
      );
    case "prompt":
      // Document icon with glow
      return (
        <g>
          <rect
            x={8}
            y={2}
            width={34}
            height={36}
            rx={3}
            stroke={color}
            strokeWidth={1.5}
            fill="none"
          />
          <line x1={14} y1={10} x2={36} y2={10} stroke={color} strokeWidth={1} opacity={0.6} />
          <line x1={14} y1={16} x2={32} y2={16} stroke={color} strokeWidth={1} opacity={0.6} />
          <line x1={14} y1={22} x2={28} y2={22} stroke={color} strokeWidth={1} opacity={0.4} />
          <text x={14} y={32} fontSize={6} fill={color} opacity={0.5} fontFamily="monospace">
            &gt;_
          </text>
        </g>
      );
    default:
      return null;
  }
}
