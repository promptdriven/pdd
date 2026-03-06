import React from "react";
import { useCurrentFrame, spring, interpolate } from "remotion";

interface DocIconProps {
  x: number;
  y: number;
  width: number;
  height: number;
  color: string;
  label: string;
  sublabel: string;
  appearStart: number;
  appearEnd: number;
  showCodeLines?: boolean;
}

export const DocIcon: React.FC<DocIconProps> = ({
  x,
  y,
  width,
  height,
  color,
  label,
  sublabel,
  appearStart,
  appearEnd,
  showCodeLines = false,
}) => {
  const frame = useCurrentFrame();

  const scale = spring({
    frame: frame - appearStart,
    fps: 30,
    config: { damping: 12, stiffness: 180 },
  });

  const labelOpacity = interpolate(
    frame,
    [appearStart + 20, appearEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  if (frame < appearStart) return null;

  const centerX = x + width / 2;
  const centerY = y + height / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: centerX,
        top: centerY,
        transform: `translate(-50%, -50%) scale(${scale})`,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        gap: 12,
      }}
    >
      {/* Document rectangle */}
      <div
        style={{
          width,
          height,
          backgroundColor: color,
          borderRadius: 12,
          opacity: 0.9,
          position: "relative",
          overflow: "hidden",
          boxShadow: `0 4px 24px ${color}44`,
        }}
      >
        {/* Corner fold */}
        <div
          style={{
            position: "absolute",
            top: 0,
            right: 0,
            width: width * 0.25,
            height: width * 0.25,
            backgroundColor: "rgba(255,255,255,0.2)",
            clipPath: "polygon(100% 0, 100% 100%, 0 0)",
          }}
        />
        {/* Code lines decoration */}
        {showCodeLines && (
          <div
            style={{
              position: "absolute",
              top: 20,
              left: 16,
              right: 16,
              display: "flex",
              flexDirection: "column",
              gap: 8,
            }}
          >
            {[0.7, 0.5, 0.85, 0.4, 0.65, 0.55, 0.75, 0.3, 0.6].map(
              (w, i) => (
                <div
                  key={i}
                  style={{
                    width: `${w * 100}%`,
                    height: 4,
                    backgroundColor: "rgba(255,255,255,0.3)",
                    borderRadius: 2,
                  }}
                />
              )
            )}
          </div>
        )}
      </div>

      {/* Labels */}
      <div
        style={{
          textAlign: "center",
          opacity: labelOpacity,
        }}
      >
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 600,
            fontSize: 22,
            color,
          }}
        >
          {label}
        </div>
        <div
          style={{
            fontFamily: "Inter, sans-serif",
            fontWeight: 400,
            fontSize: 18,
            color: "#94A3B8",
            marginTop: 4,
          }}
        >
          {sublabel}
        </div>
      </div>
    </div>
  );
};

export default DocIcon;
