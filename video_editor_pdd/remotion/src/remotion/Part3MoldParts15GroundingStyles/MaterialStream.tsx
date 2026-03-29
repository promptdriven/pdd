import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface MaterialStreamProps {
  color: string;
  label: string;
  y: number;
  width: number;
  height: number;
  streamStyle: "angular" | "smooth" | "organic";
  animStartFrame: number;
  fadeOutStart: number;
  fadeOutEnd: number;
}

const MaterialStream: React.FC<MaterialStreamProps> = ({
  color,
  label,
  y,
  width,
  height,
  streamStyle,
  animStartFrame,
  fadeOutStart,
  fadeOutEnd,
}) => {
  const frame = useCurrentFrame();

  // Stream grows from left to right
  const progress = interpolate(
    frame,
    [animStartFrame, animStartFrame + 60],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.sin),
    }
  );

  // Fade out for crossfade into Phase 2
  const opacity = interpolate(
    frame,
    [fadeOutStart, fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const currentWidth = width * progress;
  const centerX = 960;
  const startX = centerX - width / 2;

  // Texture pattern based on style
  const renderTexture = () => {
    if (streamStyle === "angular") {
      // Angular blocky texture for OOP
      const blocks: React.ReactNode[] = [];
      const blockCount = Math.floor(progress * 8);
      for (let i = 0; i < blockCount; i++) {
        const bx = startX + 20 + i * 70;
        if (bx < startX + currentWidth - 30) {
          blocks.push(
            <rect
              key={i}
              x={bx}
              y={y + 8}
              width={25}
              height={height - 16}
              rx={2}
              fill={color}
              opacity={0.5}
            />
          );
        }
      }
      return blocks;
    }

    if (streamStyle === "smooth") {
      // Smooth flowing wave for Functional
      const wavePhase = frame * 0.08;
      const points: string[] = [];
      const steps = 30;
      for (let i = 0; i <= steps; i++) {
        const t = i / steps;
        if (t * width > currentWidth) break;
        const px = startX + t * width;
        const py =
          y + height / 2 + Math.sin(t * 6 + wavePhase) * (height * 0.25);
        points.push(`${px},${py}`);
      }
      if (points.length < 2) return null;
      return (
        <polyline
          points={points.join(" ")}
          fill="none"
          stroke={color}
          strokeWidth={3}
          opacity={0.5}
        />
      );
    }

    // Organic pattern for "Your Team's Style"
    const circles: React.ReactNode[] = [];
    const circleCount = Math.floor(progress * 6);
    for (let i = 0; i < circleCount; i++) {
      const cx = startX + 40 + i * 95;
      if (cx < startX + currentWidth - 20) {
        const pulse =
          Math.sin(frame * 0.1 + i * 1.2) * 3;
        circles.push(
          <circle
            key={i}
            cx={cx}
            cy={y + height / 2}
            r={10 + pulse}
            fill={color}
            opacity={0.35}
          />
        );
      }
    }
    return circles;
  };

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        opacity,
      }}
    >
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Main gradient bar */}
        <defs>
          <linearGradient
            id={`stream-grad-${label}`}
            x1="0%"
            y1="0%"
            x2="100%"
            y2="0%"
          >
            <stop offset="0%" stopColor={color} stopOpacity={0.8} />
            <stop offset="100%" stopColor={color} stopOpacity={0.3} />
          </linearGradient>
        </defs>
        <rect
          x={startX}
          y={y}
          width={currentWidth}
          height={height}
          rx={height / 2}
          fill={`url(#stream-grad-${label})`}
        />
        {/* Texture overlay */}
        {renderTexture()}
      </svg>

      {/* Label */}
      <div
        style={{
          position: "absolute",
          top: y + height / 2 - 10,
          left: startX - 140,
          width: 130,
          textAlign: "right",
          fontFamily: "Inter, sans-serif",
          fontSize: 16,
          fontWeight: 600,
          color,
          opacity: interpolate(
            frame,
            [animStartFrame, animStartFrame + 20],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          ),
        }}
      >
        {label}
      </div>
    </div>
  );
};

export default MaterialStream;
