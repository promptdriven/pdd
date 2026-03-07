import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { Pillar } from "./Pillar";
import { ResultBox } from "./ResultBox";
import {
  PILLARS,
  ROW1_Y,
  ROW2_Y,
  CONN_1_X,
  CONN_2_X,
  EQUALS_X,
  RESULT_X,
  PILLAR_WIDTH,
  PILLAR_HEIGHT,
  CONNECTOR_GRAY,
  WHITE,
  CONN1_FADE_START,
  CONN1_FADE_END,
  CONN2_FADE_START,
  CONN2_FADE_END,
  EQUALS_FADE_START,
  EQUALS_FADE_END,
  ROW2_START,
  ROW2_STAGGER,
  ROW2_ITEMS,
  ARROWS_FADE_START,
  ARROWS_FADE_END,
  PULSE_START,
  PULSE_MID,
  PULSE_END,
  FADE_OUT_START,
  FADE_OUT_END,
} from "./constants";

export const defaultPart3Mold12ThreePillarsDiagramProps = {};

/**
 * Connector symbol (+, =) between pillars.
 */
const Connector: React.FC<{
  text: string;
  x: number;
  y: number;
  fadeStart: number;
  fadeEnd: number;
  fontSize?: number;
  color?: string;
  scaleIn?: boolean;
}> = ({
  text,
  x,
  y,
  fadeStart,
  fadeEnd,
  fontSize = 40,
  color = CONNECTOR_GRAY,
  scaleIn = false,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [fadeStart, fadeEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const scale = scaleIn
    ? interpolate(frame, [fadeStart, fadeEnd], [0.5, 1.0], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      })
    : 1;

  if (frame < fadeStart) return null;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        opacity,
        transform: `translate(-50%, -50%) scale(${scale})`,
        fontFamily: "Inter, sans-serif",
        fontWeight: 700,
        fontSize,
        color,
        lineHeight: 1,
      }}
    >
      {text}
    </div>
  );
};

/**
 * Row 2: concrete mapping labels that fade in sequentially.
 */
const Row2Labels: React.FC<{ y: number }> = ({ y }) => {
  const frame = useCurrentFrame();

  // Distribute row 2 items horizontally aligned with the pillars/connectors/result
  // Positions: Intent(under P1), +(under C1), Constraints(under P2), +(under C2), Style(under P3), =(under EQ), The Mold(under Result)
  const positions = [
    PILLARS[0].x + PILLAR_WIDTH / 2, // Intent
    CONN_1_X, // +
    PILLARS[1].x + PILLAR_WIDTH / 2, // Constraints
    CONN_2_X, // +
    PILLARS[2].x + PILLAR_WIDTH / 2, // Style
    EQUALS_X, // =
    RESULT_X + 180, // The Mold (center of result box)
  ];

  return (
    <>
      {ROW2_ITEMS.map((item, i) => {
        const itemStart = ROW2_START + i * ROW2_STAGGER;
        const itemEnd = itemStart + 10;

        const opacity = interpolate(frame, [itemStart, itemEnd], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.quad),
        });

        if (frame < itemStart) return null;

        const isTheMold = item.text === "The Mold";
        const isConnector = item.text === "+" || item.text === "=";

        return (
          <div
            key={`row2-${i}`}
            style={{
              position: "absolute",
              left: positions[i],
              top: y,
              transform: "translate(-50%, -50%)",
              opacity,
              fontFamily: "Inter, sans-serif",
              fontWeight: isTheMold ? 900 : isConnector ? 700 : 500,
              fontSize: isTheMold ? 24 : isConnector ? 28 : 20,
              color: item.color,
              lineHeight: 1,
              textShadow: isTheMold
                ? "0 0 12px rgba(255, 255, 255, 0.5)"
                : "none",
              whiteSpace: "nowrap",
            }}
          >
            {item.text}
          </div>
        );
      })}
    </>
  );
};

/**
 * Dashed connecting arrows from Row 1 pillars down to Row 2 labels.
 */
const ConnectingArrows: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [ARROWS_FADE_START, ARROWS_FADE_END], [0, 0.2], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  if (frame < ARROWS_FADE_START) return null;

  const pillarCenters = PILLARS.map((p) => p.x + PILLAR_WIDTH / 2);
  const arrowTop = ROW1_Y + PILLAR_HEIGHT / 2 + 8;
  const arrowBottom = ROW2_Y - 16;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0, opacity }}
    >
      {pillarCenters.map((cx, i) => (
        <line
          key={`arrow-${i}`}
          x1={cx}
          y1={arrowTop}
          x2={cx}
          y2={arrowBottom}
          stroke={WHITE}
          strokeWidth={1}
          strokeDasharray="4 4"
        />
      ))}
    </svg>
  );
};

export const Part3Mold12ThreePillarsDiagram: React.FC = () => {
  const frame = useCurrentFrame();

  // Overall fade in/out
  const overallOpacity = interpolate(
    frame,
    [0, 5, FADE_OUT_START, FADE_OUT_END],
    [1, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  // Pulse effect
  const pulseGlowOpacity = interpolate(
    frame,
    [PULSE_START, PULSE_MID, PULSE_END],
    [0, 0.15, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const pulseScale = interpolate(
    frame,
    [PULSE_START, PULSE_MID, PULSE_END],
    [1.0, 1.02, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.sin),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part3_mold.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Equation overlay */}
      <AbsoluteFill
        style={{
          opacity: overallOpacity,
          transform: `scale(${pulseScale})`,
          transformOrigin: "center center",
        }}
      >
        {/* Row 1: Pillars */}
        {PILLARS.map((pillar) => (
          <Pillar
            key={pillar.label}
            label={pillar.label}
            icon={pillar.icon}
            color={pillar.color}
            x={pillar.x}
            y={ROW1_Y}
            inStart={pillar.inStart}
            inEnd={pillar.inEnd}
          />
        ))}

        {/* Connectors: + signs */}
        <Connector
          text="+"
          x={CONN_1_X}
          y={ROW1_Y}
          fadeStart={CONN1_FADE_START}
          fadeEnd={CONN1_FADE_END}
        />
        <Connector
          text="+"
          x={CONN_2_X}
          y={ROW1_Y}
          fadeStart={CONN2_FADE_START}
          fadeEnd={CONN2_FADE_END}
        />

        {/* Equals sign */}
        <Connector
          text="="
          x={EQUALS_X}
          y={ROW1_Y}
          fadeStart={EQUALS_FADE_START}
          fadeEnd={EQUALS_FADE_END}
          fontSize={48}
          color={WHITE}
          scaleIn
        />

        {/* Result box */}
        <ResultBox x={RESULT_X} y={ROW1_Y} />

        {/* Connecting dashed arrows */}
        <ConnectingArrows />

        {/* Row 2: Abstract mapping labels */}
        <Row2Labels y={ROW2_Y} />

        {/* Pulse glow overlay */}
        {frame >= PULSE_START && frame <= PULSE_END && (
          <AbsoluteFill
            style={{
              backgroundColor: `rgba(255, 255, 255, ${pulseGlowOpacity})`,
              borderRadius: 20,
              pointerEvents: "none",
            }}
          />
        )}
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3Mold12ThreePillarsDiagram;
