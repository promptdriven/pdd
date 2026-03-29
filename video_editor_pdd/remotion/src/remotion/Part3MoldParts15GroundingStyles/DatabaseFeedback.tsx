import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { TEAL, MINT_GREEN } from "./constants";

interface DatabaseFeedbackProps {
  arrowStart: number;
  arrowEnd: number;
  dbAppearStart: number;
  dbAppearEnd: number;
  dashedArrowStart: number;
  dashedArrowEnd: number;
}

const DatabaseFeedback: React.FC<DatabaseFeedbackProps> = ({
  arrowStart,
  arrowEnd,
  dbAppearStart,
  dbAppearEnd,
  dashedArrowStart,
  dashedArrowEnd,
}) => {
  const frame = useCurrentFrame();

  // Arrow animation progress
  const arrowProgress = interpolate(
    frame,
    [arrowStart, arrowEnd],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Database icon fade in
  const dbOpacity = interpolate(
    frame,
    [dbAppearStart, dbAppearEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Database pulse
  const dbPulse =
    frame >= dbAppearEnd
      ? Math.sin(((frame - dbAppearEnd) / 15) * Math.PI * 2) * 0.15 + 1
      : 1;

  // Dashed arrow to future generations
  const dashedProgress = interpolate(
    frame,
    [dashedArrowStart, dashedArrowEnd],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Flow particle along the main arrow
  const particleT = arrowProgress;

  // Arrow path from right code panel to database
  const arrowFromX = 1100;
  const arrowFromY = 460;
  const arrowToX = 960;
  const arrowToY = 740;

  const particleX = arrowFromX + (arrowToX - arrowFromX) * particleT;
  const particleY = arrowFromY + (arrowToY - arrowFromY) * particleT;

  // Dashed arrow from database to future
  const dashedFromY = 840;
  const dashedToY = 940;

  // "(prompt, code)" label along arrow
  const labelOpacity = interpolate(
    frame,
    [arrowStart + 10, arrowStart + 25],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
      }}
    >
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Main flow arrow from code to database */}
        {arrowProgress > 0 && (
          <>
            <defs>
              <marker
                id="arrowhead-teal"
                markerWidth="10"
                markerHeight="7"
                refX="10"
                refY="3.5"
                orient="auto"
              >
                <polygon
                  points="0 0, 10 3.5, 0 7"
                  fill={TEAL}
                  opacity={0.7}
                />
              </marker>
            </defs>
            <line
              x1={arrowFromX}
              y1={arrowFromY}
              x2={arrowFromX + (arrowToX - arrowFromX) * arrowProgress}
              y2={arrowFromY + (arrowToY - arrowFromY) * arrowProgress}
              stroke={TEAL}
              strokeWidth={3}
              opacity={0.5}
              markerEnd={arrowProgress > 0.9 ? "url(#arrowhead-teal)" : undefined}
            />

            {/* Flow particle */}
            {arrowProgress > 0.05 && arrowProgress < 0.95 && (
              <circle
                cx={particleX}
                cy={particleY}
                r={6}
                fill={TEAL}
                opacity={0.8}
              >
                <animate
                  attributeName="r"
                  values="4;8;4"
                  dur="0.5s"
                  repeatCount="indefinite"
                />
              </circle>
            )}
          </>
        )}

        {/* Database icon (cylinder) */}
        {dbOpacity > 0 && (
          <g
            transform={`translate(960, 790) scale(${dbPulse})`}
            opacity={dbOpacity}
          >
            {/* Cylinder body */}
            <rect
              x={-40}
              y={-15}
              width={80}
              height={45}
              rx={4}
              fill={TEAL}
              opacity={0.2}
              stroke={TEAL}
              strokeWidth={2}
            />
            {/* Top ellipse */}
            <ellipse
              cx={0}
              cy={-15}
              rx={40}
              ry={12}
              fill={TEAL}
              opacity={0.25}
              stroke={TEAL}
              strokeWidth={2}
            />
            {/* Bottom ellipse */}
            <ellipse
              cx={0}
              cy={30}
              rx={40}
              ry={12}
              fill="none"
              stroke={TEAL}
              strokeWidth={2}
            />
            {/* Data lines inside */}
            <line
              x1={-20}
              y1={0}
              x2={20}
              y2={0}
              stroke={TEAL}
              strokeWidth={1.5}
              opacity={0.5}
            />
            <line
              x1={-15}
              y1={10}
              x2={15}
              y2={10}
              stroke={TEAL}
              strokeWidth={1.5}
              opacity={0.4}
            />
          </g>
        )}

        {/* Dashed arrow to future generations */}
        {dashedProgress > 0 && (
          <>
            <defs>
              <marker
                id="arrowhead-teal-dashed"
                markerWidth="8"
                markerHeight="6"
                refX="8"
                refY="3"
                orient="auto"
              >
                <polygon
                  points="0 0, 8 3, 0 6"
                  fill={TEAL}
                  opacity={0.4}
                />
              </marker>
            </defs>
            <line
              x1={960}
              y1={dashedFromY}
              x2={960}
              y2={dashedFromY + (dashedToY - dashedFromY) * dashedProgress}
              stroke={TEAL}
              strokeWidth={2}
              strokeDasharray="8 4"
              opacity={0.35}
              markerEnd={
                dashedProgress > 0.9
                  ? "url(#arrowhead-teal-dashed)"
                  : undefined
              }
            />
          </>
        )}
      </svg>

      {/* "(prompt, code)" label along arrow */}
      {arrowProgress > 0.1 && (
        <div
          style={{
            position: "absolute",
            left: particleX + 15,
            top: particleY - 10,
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 11,
            color: MINT_GREEN,
            opacity: labelOpacity * 0.85,
            whiteSpace: "nowrap",
          }}
        >
          (prompt, code)
        </div>
      )}

      {/* Database label */}
      {dbOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: 960 - 80,
            top: 838,
            width: 160,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            fontWeight: 600,
            color: TEAL,
            opacity: dbOpacity * 0.9,
          }}
        >
          Grounding Database
        </div>
      )}

      {/* "Future Generations" label */}
      {dashedProgress > 0.5 && (
        <div
          style={{
            position: "absolute",
            left: 960 - 80,
            top: 950,
            width: 160,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 13,
            fontWeight: 500,
            color: TEAL,
            opacity: interpolate(
              dashedProgress,
              [0.5, 1],
              [0, 0.7],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
          }}
        >
          Future Generations
        </div>
      )}

      {/* pdd fix terminal note */}
      {dbOpacity > 0.5 && (
        <div
          style={{
            position: "absolute",
            left: 1060,
            top: 790,
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: 11,
            color: MINT_GREEN,
            opacity: interpolate(
              dbOpacity,
              [0.5, 1],
              [0, 0.7],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
            whiteSpace: "nowrap",
          }}
        >
          pdd fix → cloud
        </div>
      )}
    </div>
  );
};

export default DatabaseFeedback;
