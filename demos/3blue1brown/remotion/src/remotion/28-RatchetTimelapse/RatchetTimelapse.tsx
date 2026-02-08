import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing, spring } from "remotion";
import { COLORS, BEATS, ACCUMULATING_TESTS, RatchetTimelapsePropsType, RATCHET_FPS } from "./constants";

/** Number of teeth on the ratchet gear */
const GEAR_TEETH = 12;
/** Gear visual radius */
const GEAR_RADIUS = 50;
/** Tooth height */
const TOOTH_HEIGHT = 14;

/**
 * SVG ratchet gear component with triangular teeth and a pawl.
 * The gear rotates one tooth per wall addition. The pawl engages
 * after each click to prevent backward movement.
 */
const RatchetGear: React.FC<{
  /** Number of teeth the gear has advanced */
  teethAdvanced: number;
  /** Current frame for spring animation */
  currentFrame: number;
  /** X position */
  cx: number;
  /** Y position */
  cy: number;
}> = ({ teethAdvanced, currentFrame, cx, cy }) => {
  // Each tooth advancement = 360/GEAR_TEETH degrees
  const targetAngle = teethAdvanced * (360 / GEAR_TEETH);

  // Spring-based rotation for snappy click feel
  const springValue = spring({
    frame: currentFrame,
    fps: RATCHET_FPS,
    config: {
      damping: 18,
      stiffness: 200,
      mass: 0.4,
    },
  });

  // Lerp toward target angle with spring
  const smoothAngle = targetAngle * springValue + (1 - springValue) * Math.max(0, targetAngle - 360 / GEAR_TEETH);

  // Generate gear path with triangular teeth
  const gearPath = (() => {
    const points: string[] = [];
    for (let i = 0; i < GEAR_TEETH; i++) {
      const angle1 = (i / GEAR_TEETH) * Math.PI * 2 - Math.PI / 2;
      const angle2 = ((i + 0.3) / GEAR_TEETH) * Math.PI * 2 - Math.PI / 2;
      const angle3 = ((i + 0.5) / GEAR_TEETH) * Math.PI * 2 - Math.PI / 2;
      const angle4 = ((i + 0.8) / GEAR_TEETH) * Math.PI * 2 - Math.PI / 2;

      // Inner point
      const ix1 = Math.cos(angle1) * GEAR_RADIUS;
      const iy1 = Math.sin(angle1) * GEAR_RADIUS;
      // Rising to tooth tip
      const ox2 = Math.cos(angle2) * (GEAR_RADIUS + TOOTH_HEIGHT);
      const oy2 = Math.sin(angle2) * (GEAR_RADIUS + TOOTH_HEIGHT);
      // Tooth tip
      const ox3 = Math.cos(angle3) * (GEAR_RADIUS + TOOTH_HEIGHT);
      const oy3 = Math.sin(angle3) * (GEAR_RADIUS + TOOTH_HEIGHT);
      // Back down
      const ix4 = Math.cos(angle4) * GEAR_RADIUS;
      const iy4 = Math.sin(angle4) * GEAR_RADIUS;

      if (i === 0) {
        points.push(`M ${ix1} ${iy1}`);
      } else {
        points.push(`L ${ix1} ${iy1}`);
      }
      points.push(`L ${ox2} ${oy2}`);
      points.push(`L ${ox3} ${oy3}`);
      points.push(`L ${ix4} ${iy4}`);
    }
    points.push("Z");
    return points.join(" ");
  })();

  // Pawl (triangular piece that catches teeth, positioned to the right of gear)
  const pawlX = GEAR_RADIUS + TOOTH_HEIGHT + 8;
  const pawlY = 0;

  // Pawl engagement animation -- slight bounce on each click
  const pawlBounce = teethAdvanced > 0
    ? spring({
        frame: currentFrame,
        fps: RATCHET_FPS,
        config: { damping: 12, stiffness: 300, mass: 0.3 },
      })
    : 0;

  const pawlOffset = (1 - pawlBounce) * 8;

  return (
    <g transform={`translate(${cx}, ${cy})`}>
      {/* Gear body (rotates) */}
      <g transform={`rotate(${smoothAngle})`}>
        {/* Gear teeth */}
        <path
          d={gearPath}
          fill="rgba(138, 155, 168, 0.3)"
          stroke="#8A9BA8"
          strokeWidth={2}
        />
        {/* Center hub */}
        <circle
          r={GEAR_RADIUS * 0.35}
          fill="rgba(138, 155, 168, 0.2)"
          stroke="#8A9BA8"
          strokeWidth={2}
        />
        {/* Center dot */}
        <circle
          r={4}
          fill="#8A9BA8"
        />
      </g>

      {/* Pawl (does not rotate with gear) */}
      <g transform={`translate(${pawlX + pawlOffset}, ${pawlY})`}>
        <polygon
          points="-18,-8 0,0 -18,8"
          fill="rgba(217, 148, 74, 0.5)"
          stroke={COLORS.WALLS_AMBER}
          strokeWidth={1.5}
        />
      </g>

      {/* Axle mount */}
      <circle
        r={2}
        fill="#666"
      />

      {/* Label */}
      <text
        y={GEAR_RADIUS + TOOTH_HEIGHT + 30}
        textAnchor="middle"
        fill="#666"
        fontSize={13}
        fontFamily="sans-serif"
      >
        Ratchet: Only Forward
      </text>
    </g>
  );
};

export const RatchetTimelapse: React.FC<RatchetTimelapsePropsType> = ({
  maxWalls = 15,
}) => {
  const frame = useCurrentFrame();

  // Initial walls visibility
  const initialOpacity = interpolate(
    frame,
    [BEATS.INITIAL_WALLS_START, BEATS.INITIAL_WALLS_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Calculate how many walls are visible during timelapse
  const wallCount = frame < BEATS.TIMELAPSE_START
    ? 5 // Start with 5 walls
    : Math.min(
        5 + Math.floor((frame - BEATS.TIMELAPSE_START) / BEATS.WALL_ACCUMULATION_RATE),
        maxWalls
      );

  // Number of new walls added (for gear advancement)
  const newWallsAdded = wallCount - 5;

  // Frame of the most recent wall addition (for spring animation reset)
  const lastWallFrame = newWallsAdded > 0
    ? BEATS.TIMELAPSE_START + (newWallsAdded - 1) * BEATS.WALL_ACCUMULATION_RATE
    : 0;

  // Counter visibility
  const counterOpacity = interpolate(
    frame,
    [BEATS.COUNTER_START, BEATS.COUNTER_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Insight text
  const insightOpacity = interpolate(
    frame,
    [BEATS.INSIGHT_START, BEATS.INSIGHT_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Wall layout configuration
  const columns = 3;
  const wallWidth = 180;
  const wallHeight = 50;
  const gap = 12;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Wall grid */}
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: "50%",
          transform: "translate(-50%, -50%)",
          display: "grid",
          gridTemplateColumns: `repeat(${columns}, ${wallWidth}px)`,
          gap: gap,
          opacity: initialOpacity,
        }}
      >
        {ACCUMULATING_TESTS.slice(0, wallCount).map((test, i) => {
          // Spring animation for each new wall
          const wallAppearFrame = i < 3
            ? 0
            : BEATS.TIMELAPSE_START + (i - 3) * BEATS.WALL_ACCUMULATION_RATE;

          const wallScale = spring({
            frame: frame - wallAppearFrame,
            fps: RATCHET_FPS,
            config: {
              damping: 15,
              stiffness: 120,
              mass: 0.5,
            },
          });

          const isNewWall = frame - wallAppearFrame < 30;

          return (
            <div
              key={i}
              style={{
                width: wallWidth,
                height: wallHeight,
                background: `rgba(217, 148, 74, ${isNewWall ? 0.5 : 0.3})`,
                border: `2px solid ${COLORS.WALLS_AMBER}`,
                borderRadius: 6,
                display: "flex",
                alignItems: "center",
                justifyContent: "center",
                fontSize: 11,
                fontFamily: "JetBrains Mono, monospace",
                color: COLORS.WALLS_AMBER,
                transform: `scale(${Math.min(wallScale, 1)})`,
                boxShadow: isNewWall
                  ? `0 0 20px ${COLORS.WALLS_AMBER}`
                  : "none",
                opacity: wallScale > 0 ? 1 : 0,
              }}
            >
              {test}
            </div>
          );
        })}
      </div>

      {/* Counter */}
      {counterOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: 100,
            right: 100,
            opacity: counterOpacity,
            textAlign: "right",
          }}
        >
          <div
            style={{
              fontSize: 48,
              fontWeight: "bold",
              color: COLORS.COUNTER_BLUE,
              fontFamily: "sans-serif",
            }}
          >
            {wallCount}
          </div>
          <div
            style={{
              fontSize: 16,
              color: COLORS.LABEL_GRAY,
            }}
          >
            test constraints
          </div>
        </div>
      )}

      {/* SVG Ratchet gear mechanism (replaces text placeholder) */}
      {frame >= BEATS.TIMELAPSE_START && (
        <div
          style={{
            position: "absolute",
            bottom: 170,
            left: 120,
            opacity: interpolate(
              frame,
              [BEATS.TIMELAPSE_START, BEATS.TIMELAPSE_START + 30],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
          }}
        >
          <svg width={200} height={180} viewBox="-100 -90 200 180">
            <RatchetGear
              teethAdvanced={newWallsAdded}
              currentFrame={frame - lastWallFrame}
              cx={0}
              cy={0}
            />
          </svg>
        </div>
      )}

      {/* Insight text */}
      {insightOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 80,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: insightOpacity,
          }}
        >
          <div
            style={{
              fontSize: 24,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
              marginBottom: 12,
            }}
          >
            Each bug caught becomes a permanent constraint.
          </div>
          <div
            style={{
              fontSize: 18,
              color: COLORS.LABEL_GRAY,
            }}
          >
            The mold can only get more precise over time.
          </div>
        </div>
      )}

      {/* Section header */}
      <div
        style={{
          position: "absolute",
          top: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: initialOpacity,
        }}
      >
        <span
          style={{
            fontSize: 24,
            fontFamily: "sans-serif",
            color: COLORS.WALLS_AMBER,
            fontWeight: "bold",
          }}
        >
          The Ratchet Effect
        </span>
        <div
          style={{
            fontSize: 16,
            color: COLORS.LABEL_GRAY,
            marginTop: 8,
          }}
        >
          Time-lapse: walls accumulating over development
        </div>
      </div>
    </AbsoluteFill>
  );
};
