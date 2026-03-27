import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  STREAM_WIDTH,
  STREAM_HEIGHT,
  CANVAS_WIDTH,
  type MaterialStreamData,
} from "./constants";

interface MaterialStreamProps {
  stream: MaterialStreamData;
  y: number;
  delayFrames: number;
}

const MaterialStream: React.FC<MaterialStreamProps> = ({
  stream,
  y,
  delayFrames,
}) => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - delayFrames);

  // Stream flows in from left
  const progress = interpolate(localFrame, [0, 60], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.sin),
  });

  const barWidth = STREAM_WIDTH * progress;
  const barX = (CANVAS_WIDTH - STREAM_WIDTH) / 2;

  // Opacity fade-in
  const opacity = interpolate(localFrame, [0, 15], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Angular texture blocks for OOP
  const renderAngularTexture = () => {
    const blockCount = 8;
    return Array.from({ length: blockCount }).map((_, i) => {
      const blockX = (barWidth / blockCount) * i;
      const blockW = barWidth / blockCount - 3;
      if (blockW <= 0) return null;
      return (
        <rect
          key={i}
          x={blockX + 2}
          y={4}
          width={Math.max(0, blockW)}
          height={STREAM_HEIGHT - 8}
          rx={2}
          fill={stream.color}
          opacity={0.5 + (i % 2) * 0.3}
        />
      );
    });
  };

  // Smooth flowing shapes for Functional
  const renderSmoothTexture = () => {
    const waveOffset = localFrame * 2;
    const points: string[] = [];
    const steps = 40;
    for (let i = 0; i <= steps; i++) {
      const px = (barWidth / steps) * i;
      const py =
        STREAM_HEIGHT / 2 +
        Math.sin((i / steps) * Math.PI * 4 + waveOffset * 0.05) * 8;
      points.push(`${px},${py}`);
    }
    // Close the path along the bottom
    points.push(`${barWidth},${STREAM_HEIGHT}`);
    points.push(`0,${STREAM_HEIGHT}`);
    return (
      <polygon
        points={points.join(" ")}
        fill={stream.color}
        opacity={0.6}
      />
    );
  };

  // Organic pattern for Your Team's Style
  const renderOrganicTexture = () => {
    const blobCount = 5;
    return Array.from({ length: blobCount }).map((_, i) => {
      const cx = (barWidth / (blobCount + 1)) * (i + 1);
      const baseR = 12 + Math.sin(i * 1.5 + localFrame * 0.03) * 4;
      const ry = baseR * 0.7;
      if (cx <= 0 || cx > barWidth) return null;
      return (
        <ellipse
          key={i}
          cx={cx}
          cy={STREAM_HEIGHT / 2}
          rx={baseR}
          ry={ry}
          fill={stream.color}
          opacity={0.4 + Math.sin(i + localFrame * 0.05) * 0.2}
        />
      );
    });
  };

  const renderTexture = () => {
    switch (stream.style) {
      case "angular":
        return renderAngularTexture();
      case "smooth":
        return renderSmoothTexture();
      case "organic":
        return renderOrganicTexture();
    }
  };

  return (
    <div
      style={{
        position: "absolute",
        left: barX,
        top: y,
        opacity,
        width: STREAM_WIDTH,
        height: STREAM_HEIGHT + 30,
      }}
    >
      {/* Stream bar */}
      <svg
        width={STREAM_WIDTH}
        height={STREAM_HEIGHT}
        style={{ overflow: "visible" }}
      >
        {/* Background track */}
        <rect
          x={0}
          y={0}
          width={STREAM_WIDTH}
          height={STREAM_HEIGHT}
          rx={STREAM_HEIGHT / 2}
          fill={stream.color}
          opacity={0.1}
        />
        {/* Clip for the animated fill */}
        <defs>
          <clipPath id={`stream-clip-${stream.style}`}>
            <rect
              x={0}
              y={0}
              width={barWidth}
              height={STREAM_HEIGHT}
              rx={STREAM_HEIGHT / 2}
            />
          </clipPath>
        </defs>
        <g clipPath={`url(#stream-clip-${stream.style})`}>
          {/* Solid fill */}
          <rect
            x={0}
            y={0}
            width={STREAM_WIDTH}
            height={STREAM_HEIGHT}
            rx={STREAM_HEIGHT / 2}
            fill={stream.color}
            opacity={0.3}
          />
          {/* Texture overlay */}
          {renderTexture()}
        </g>
      </svg>
      {/* Label */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 16,
          fontWeight: 600,
          color: stream.color,
          marginTop: 6,
          textAlign: "center",
        }}
      >
        {stream.label}
      </div>
    </div>
  );
};

export default MaterialStream;
