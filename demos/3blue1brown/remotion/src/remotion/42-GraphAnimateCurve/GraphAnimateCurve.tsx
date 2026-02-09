import React, { useMemo } from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, GraphAnimateCurvePropsType } from "./constants";

// Component for the curve marker with trail effect
const CurveMarker: React.FC<{
  x: number;
  y: number;
  progress: number;
}> = ({ x, y, progress }) => {
  // Generate trail points
  const trailPoints = useMemo(() => {
    const points = [];
    for (let i = 0; i < 10; i++) {
      const trailProgress = Math.max(0, progress - i * 0.02);
      const trailX = 100 + trailProgress * 1300;
      const trailY = 650 - 500 * (1 / (trailProgress * 2 + 0.3));
      points.push({ x: trailX, y: trailY, opacity: 1 - i * 0.1 });
    }
    return points;
  }, [progress]);

  return (
    <svg
      style={{
        position: "absolute",
        width: "100%",
        height: "100%",
        pointerEvents: "none",
      }}
    >
      <defs>
        <filter id="markerGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="6" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Trail */}
      {trailPoints.map((point, i) => (
        <circle
          key={i}
          cx={point.x}
          cy={point.y}
          r={4}
          fill={`rgba(255, 255, 255, ${point.opacity * 0.3})`}
        />
      ))}

      {/* Main marker */}
      <circle
        cx={x}
        cy={y}
        r={12}
        fill={COLORS.MARKER_WHITE}
        filter="url(#markerGlow)"
      />
    </svg>
  );
};

// Prompt icon component that shrinks as marker moves right
const PromptIcon: React.FC<{
  scale: number;
  position: { x: number; y: number };
}> = ({ scale, position }) => {
  // Fixed line widths for consistency (no random values)
  const lineWidths = [85, 70, 90, 65, 80, 75, 85, 60];

  return (
    <div
      style={{
        position: "absolute",
        left: position.x,
        top: position.y,
        transform: `translate(-50%, -50%) scale(${scale})`,
        transformOrigin: "center",
      }}
    >
      <div
        style={{
          width: 200,
          height: 250,
          backgroundColor: COLORS.NOZZLE_BLUE,
          borderRadius: 8,
          display: "flex",
          flexDirection: "column",
          padding: 15,
          boxShadow: `0 0 30px rgba(74, 144, 217, 0.5)`,
        }}
      >
        {/* File header */}
        <div
          style={{
            fontSize: 14,
            color: "rgba(255, 255, 255, 0.7)",
            marginBottom: 10,
            fontFamily: "monospace",
          }}
        >
          parser.prompt
        </div>

        {/* Prompt lines */}
        {lineWidths.map((width, i) => (
          <div
            key={i}
            style={{
              height: 8,
              backgroundColor: "rgba(255, 255, 255, 0.3)",
              marginBottom: 6,
              borderRadius: 4,
              width: `${width}%`,
            }}
          />
        ))}
      </div>
    </div>
  );
};

// Test walls component that multiplies as marker moves right
const TestWalls: React.FC<{
  count: number;
  position: { x: number; y: number };
  scale: number;
}> = ({ count, position, scale }) => {
  const walls = useMemo(() => {
    return [...Array(count)].map((_, i) => ({
      x: (i % 5) * 35,
      y: Math.floor(i / 5) * 45,
      key: i,
    }));
  }, [count]);

  return (
    <div
      style={{
        position: "absolute",
        left: position.x,
        top: position.y,
        transform: `translate(-50%, -50%) scale(${scale})`,
        transformOrigin: "center",
      }}
    >
      {walls.map((wall) => (
        <div
          key={wall.key}
          style={{
            position: "absolute",
            left: wall.x,
            top: wall.y,
            width: 25,
            height: 35,
            backgroundColor: COLORS.WALLS_AMBER,
            borderRadius: 4,
            boxShadow: `0 0 15px rgba(217, 148, 74, 0.5)`,
          }}
        />
      ))}
    </div>
  );
};

// Position label component
const PositionLabel: React.FC<{
  text: string;
  positionSide: "left" | "right";
  active: boolean;
}> = ({ text, positionSide, active }) => {
  const opacity = active ? 1 : 0.3;
  const x = positionSide === "left" ? 300 : 1620;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        bottom: 80,
        transform: "translateX(-50%)",
        fontSize: 18,
        fontWeight: "bold",
        color: COLORS.LABEL_WHITE,
        opacity,
        transition: "opacity 0.3s ease",
        fontFamily: "sans-serif",
      }}
    >
      {text}
    </div>
  );
};

// Static precision graph (from Section 4.4)
const PrecisionGraphStatic: React.FC = () => {
  // Generate curve path points for the inverse relationship
  const curvePath = useMemo(() => {
    const points: string[] = [];
    for (let i = 0; i <= 100; i++) {
      const progress = i / 100;
      const x = 100 + progress * 1300;
      const y = 650 - 500 * (1 / (progress * 2 + 0.3));
      if (i === 0) {
        points.push(`M ${x} ${y}`);
      } else {
        points.push(`L ${x} ${y}`);
      }
    }
    return points.join(" ");
  }, []);

  return (
    <svg
      style={{
        position: "absolute",
        width: "100%",
        height: "100%",
      }}
    >
      {/* Y-axis */}
      <line
        x1={100}
        y1={150}
        x2={100}
        y2={650}
        stroke={COLORS.AXIS_GRAY}
        strokeWidth={2}
      />
      {/* X-axis */}
      <line
        x1={100}
        y1={650}
        x2={1400}
        y2={650}
        stroke={COLORS.AXIS_GRAY}
        strokeWidth={2}
      />
      {/* Y-axis label */}
      <text
        x={100}
        y={400}
        fill={COLORS.LABEL_GRAY}
        fontSize={16}
        fontFamily="sans-serif"
        transform="rotate(-90, 100, 400)"
        textAnchor="middle"
      >
        Required Prompt Precision
      </text>
      {/* X-axis label */}
      <text
        x={800}
        y={820}
        fill={COLORS.LABEL_GRAY}
        fontSize={16}
        fontFamily="sans-serif"
        textAnchor="middle"
      >
        Number of Tests
      </text>

      {/* Inverse curve */}
      <path
        d={curvePath}
        fill="none"
        stroke={COLORS.CURVE_BLUE}
        strokeWidth={3}
        opacity={0.8}
      />
    </svg>
  );
};

export const GraphAnimateCurve: React.FC<GraphAnimateCurvePropsType> = ({
  showLabels = true,
}) => {
  const frame = useCurrentFrame();

  // Setup phase opacity
  const setupOpacity = interpolate(
    frame,
    [BEATS.SETUP_START, BEATS.SETUP_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Marker position along curve (0 to 1)
  const curveProgress = interpolate(
    frame,
    [BEATS.TRAVEL_START, BEATS.TRAVEL_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Calculate marker position on curve
  const markerX = 100 + curveProgress * 1300;
  const markerY = 650 - 500 * (1 / (curveProgress * 2 + 0.3));

  // Prompt size (large at start, small at end)
  const promptScale = interpolate(curveProgress, [0, 1], [1, 0.3]);

  // Number of test walls (increases as marker moves right)
  const wallCount = Math.floor(interpolate(curveProgress, [0, 1], [2, 25]));

  // Final pulse effect
  const finalPulse =
    frame > BEATS.ARRIVE_START
      ? 1 + Math.sin((frame - BEATS.ARRIVE_START) * 0.1) * 0.05
      : 1;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <div style={{ opacity: setupOpacity }}>
        {/* Graph from Section 4.4 */}
        <PrecisionGraphStatic />

        {/* Marker on curve */}
        <CurveMarker x={markerX} y={markerY} progress={curveProgress} />

        {/* Prompt size indicator */}
        <PromptIcon
          scale={promptScale * finalPulse}
          position={{ x: 300, y: 400 }}
        />

        {/* Test walls */}
        <TestWalls
          count={wallCount}
          position={{ x: 1550, y: 400 }}
          scale={finalPulse}
        />

        {/* Position labels */}
        {showLabels && (
          <>
            <PositionLabel
              text="FEW TESTS"
              positionSide="left"
              active={curveProgress < 0.3}
            />
            <PositionLabel
              text="MANY TESTS"
              positionSide="right"
              active={curveProgress > 0.7}
            />
          </>
        )}

        {/* Title */}
        <div
          style={{
            position: "absolute",
            top: 40,
            left: 0,
            right: 0,
            textAlign: "center",
          }}
        >
          <span
            style={{
              fontSize: 28,
              fontFamily: "sans-serif",
              color: COLORS.LABEL_WHITE,
              fontWeight: "bold",
            }}
          >
            The Precision Tradeoff
          </span>
        </div>
      </div>
    </AbsoluteFill>
  );
};
