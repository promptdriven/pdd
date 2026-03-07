import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing, spring } from "remotion";
import { Pillar } from "./Pillar";
import { Connector } from "./Connector";
import { ResultBox } from "./ResultBox";
import {
  BG_COLOR,
  TOTAL_FRAMES,
  ROW_1_Y,
  ROW_2_Y,
  ROW_2_ITEMS,
  ROW_2_FONT_SIZE,
  MOLD_FONT_SIZE,
  MOLD_TEXT_SHADOW,
  SLIDE_UP_DISTANCE,
  PILLAR_1_START,
  PILLAR_1_END,
  PLUS_1_START,
  PLUS_1_END,
  PILLAR_2_START,
  PILLAR_2_END,
  PLUS_2_START,
  PLUS_2_END,
  PILLAR_3_START,
  PILLAR_3_END,
  EQUALS_START,
  EQUALS_END,
  RESULT_START,
  RESULT_END,
  ROW_2_START,
  ROW_2_STAGGER,
  ARROWS_START,
  ARROWS_END,
  PULSE_START,
  PULSE_MID,
  PULSE_END,
  FADE_OUT_START,
  FADE_OUT_END,
} from "./constants";

export const defaultPart3Mold12ThreePillarsDiagramProps = {};

const clamp = { extrapolateLeft: "clamp" as const, extrapolateRight: "clamp" as const };

export const Part3Mold12ThreePillarsDiagram: React.FC = () => {
  const frame = useCurrentFrame();

  // Overall fade (visible from frame 0, fade out at end)
  const overallOpacity = interpolate(
    frame,
    [0, 5, FADE_OUT_START, FADE_OUT_END],
    [1, 1, 1, 0],
    clamp,
  );

  // Pillar 1 "Prompt" — spring slide up
  const pillar1Spring = spring({
    frame: frame - PILLAR_1_START,
    fps: 30,
    config: { damping: 14, stiffness: 200 },
  });
  const pillar1Opacity = interpolate(frame, [PILLAR_1_START, PILLAR_1_END], [0, 1], clamp);
  const pillar1TranslateY = interpolate(pillar1Spring, [0, 1], [SLIDE_UP_DISTANCE, 0]);

  // Plus 1
  const plus1Opacity = interpolate(frame, [PLUS_1_START, PLUS_1_END], [0, 1], {
    ...clamp,
    easing: Easing.out(Easing.quad),
  });

  // Pillar 2 "Tests" — spring slide up
  const pillar2Spring = spring({
    frame: frame - PILLAR_2_START,
    fps: 30,
    config: { damping: 14, stiffness: 200 },
  });
  const pillar2Opacity = interpolate(frame, [PILLAR_2_START, PILLAR_2_END], [0, 1], clamp);
  const pillar2TranslateY = interpolate(pillar2Spring, [0, 1], [SLIDE_UP_DISTANCE, 0]);

  // Plus 2
  const plus2Opacity = interpolate(frame, [PLUS_2_START, PLUS_2_END], [0, 1], {
    ...clamp,
    easing: Easing.out(Easing.quad),
  });

  // Pillar 3 "Grounding" — spring slide up
  const pillar3Spring = spring({
    frame: frame - PILLAR_3_START,
    fps: 30,
    config: { damping: 14, stiffness: 200 },
  });
  const pillar3Opacity = interpolate(frame, [PILLAR_3_START, PILLAR_3_END], [0, 1], clamp);
  const pillar3TranslateY = interpolate(pillar3Spring, [0, 1], [SLIDE_UP_DISTANCE, 0]);

  // Equals sign — scale 0.5→1.0 + fade
  const equalsOpacity = interpolate(frame, [EQUALS_START, EQUALS_END], [0, 1], {
    ...clamp,
    easing: Easing.out(Easing.quad),
  });
  const equalsScale = interpolate(frame, [EQUALS_START, EQUALS_END], [0.5, 1.0], {
    ...clamp,
    easing: Easing.out(Easing.quad),
  });

  // Result "Complete Specification" — fade in with glow
  const resultOpacity = interpolate(frame, [RESULT_START, RESULT_END], [0, 1], {
    ...clamp,
    easing: Easing.out(Easing.poly(4)),
  });

  // Row 2 label opacities (staggered)
  const row2Opacities = ROW_2_ITEMS.map((_, i) =>
    interpolate(
      frame,
      [ROW_2_START + i * ROW_2_STAGGER, ROW_2_START + i * ROW_2_STAGGER + 10],
      [0, 1],
      { ...clamp, easing: Easing.out(Easing.quad) },
    ),
  );

  // Connecting dashed arrows opacity
  const arrowsOpacity = interpolate(frame, [ARROWS_START, ARROWS_END], [0, 0.2], {
    ...clamp,
    easing: Easing.out(Easing.quad),
  });

  // Pulse effect
  const pulseGlowOpacity = interpolate(frame, [PULSE_START, PULSE_MID, PULSE_END], [0, 0.15, 0], clamp);
  const pulseScale = interpolate(frame, [PULSE_START, PULSE_MID, PULSE_END], [1.0, 1.02, 1.0], {
    ...clamp,
    easing: Easing.inOut(Easing.sin),
  });

  // Horizontal layout positions for Row 1
  // Elements: Pillar(200) + gap(40) + Plus(40) + gap(40) + Pillar(200) + gap(40) + Plus(40) + gap(40) + Pillar(200) + gap(40) + Equals(40) + gap(40) + Result(360)
  // Total: 200+40+40+40+200+40+40+40+200+40+40+40+360 = 1320
  const totalRow1Width = 1320;
  const row1StartX = (1920 - totalRow1Width) / 2;

  // Element x positions (left edge of each element)
  const positions = {
    pillar1: row1StartX,
    plus1: row1StartX + 200 + 40,
    pillar2: row1StartX + 200 + 40 + 40 + 40,
    plus2: row1StartX + 200 + 40 + 40 + 40 + 200 + 40,
    pillar3: row1StartX + 200 + 40 + 40 + 40 + 200 + 40 + 40 + 40,
    equals: row1StartX + 200 + 40 + 40 + 40 + 200 + 40 + 40 + 40 + 200 + 40,
    result: row1StartX + 200 + 40 + 40 + 40 + 200 + 40 + 40 + 40 + 200 + 40 + 40 + 40,
  };

  // Row 2 positions: map each text below its corresponding Row 1 element
  // "Intent" below Pillar1, "+" below Plus1, "Constraints" below Pillar2,
  // "+" below Plus2, "Style" below Pillar3, "=" below Equals, "The Mold" below Result
  const row2CenterXs = [
    positions.pillar1 + 100,   // center of Pillar 1
    positions.plus1 + 20,      // center of Plus 1
    positions.pillar2 + 100,   // center of Pillar 2
    positions.plus2 + 20,      // center of Plus 2
    positions.pillar3 + 100,   // center of Pillar 3
    positions.equals + 20,     // center of Equals
    positions.result + 180,    // center of Result
  ];

  // Dashed arrow lines: from bottom of each pillar to top of its Row 2 label
  const arrowPairs = [
    { x: positions.pillar1 + 100, y1: ROW_1_Y + 100, y2: ROW_2_Y - 10 },
    { x: positions.pillar2 + 100, y1: ROW_1_Y + 100, y2: ROW_2_Y - 10 },
    { x: positions.pillar3 + 100, y1: ROW_1_Y + 100, y2: ROW_2_Y - 10 },
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <div
        style={{
          width: 1920,
          height: 1080,
          position: "relative",
          opacity: overallOpacity,
          transform: `scale(${pulseScale})`,
          transformOrigin: "center center",
        }}
      >
        {/* Row 1: Equation pillars */}
        {/* Pillar 1: Prompt */}
        <div style={{ position: "absolute", left: positions.pillar1, top: ROW_1_Y }}>
          <Pillar
            label="Prompt"
            icon="document"
            color="#F59E0B"
            opacity={pillar1Opacity}
            translateY={pillar1TranslateY}
          />
        </div>

        {/* Plus 1 */}
        <div
          style={{
            position: "absolute",
            left: positions.plus1,
            top: ROW_1_Y,
            height: 100,
            display: "flex",
            alignItems: "center",
          }}
        >
          <Connector text="+" opacity={plus1Opacity} />
        </div>

        {/* Pillar 2: Tests */}
        <div style={{ position: "absolute", left: positions.pillar2, top: ROW_1_Y }}>
          <Pillar
            label="Tests"
            icon="checkmark"
            color="#22C55E"
            opacity={pillar2Opacity}
            translateY={pillar2TranslateY}
          />
        </div>

        {/* Plus 2 */}
        <div
          style={{
            position: "absolute",
            left: positions.plus2,
            top: ROW_1_Y,
            height: 100,
            display: "flex",
            alignItems: "center",
          }}
        >
          <Connector text="+" opacity={plus2Opacity} />
        </div>

        {/* Pillar 3: Grounding */}
        <div style={{ position: "absolute", left: positions.pillar3, top: ROW_1_Y }}>
          <Pillar
            label="Grounding"
            icon="loop"
            color="#A855F7"
            opacity={pillar3Opacity}
            translateY={pillar3TranslateY}
          />
        </div>

        {/* Equals */}
        <div
          style={{
            position: "absolute",
            left: positions.equals,
            top: ROW_1_Y,
            height: 100,
            display: "flex",
            alignItems: "center",
          }}
        >
          <Connector text="=" opacity={equalsOpacity} scale={equalsScale} isEquals />
        </div>

        {/* Result: Complete Specification */}
        <div style={{ position: "absolute", left: positions.result, top: ROW_1_Y }}>
          <ResultBox opacity={resultOpacity} />
        </div>

        {/* Connecting dashed arrows (only for the 3 pillars) */}
        <svg
          width={1920}
          height={1080}
          style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
        >
          {arrowPairs.map((arrow, i) => (
            <line
              key={i}
              x1={arrow.x}
              y1={arrow.y1}
              x2={arrow.x}
              y2={arrow.y2}
              stroke="#FFFFFF"
              strokeWidth={1}
              strokeDasharray="4 4"
              opacity={arrowsOpacity}
            />
          ))}
        </svg>

        {/* Row 2: Abstract mapping labels */}
        {ROW_2_ITEMS.map((item, i) => {
          const isMold = item.text === "The Mold";
          const isConnector = item.text === "+" || item.text === "=";
          return (
            <div
              key={i}
              style={{
                position: "absolute",
                left: row2CenterXs[i],
                top: ROW_2_Y,
                transform: "translateX(-50%)",
                fontFamily: "Inter, sans-serif",
                fontWeight: isMold ? 900 : isConnector ? 700 : 500,
                fontSize: isMold ? MOLD_FONT_SIZE : ROW_2_FONT_SIZE,
                color: item.color,
                opacity: row2Opacities[i],
                textShadow: isMold ? MOLD_TEXT_SHADOW : "none",
                whiteSpace: "nowrap",
              }}
            >
              {item.text}
            </div>
          );
        })}

        {/* Pulse white glow overlay */}
        {pulseGlowOpacity > 0 && (
          <div
            style={{
              position: "absolute",
              top: 0,
              left: 0,
              width: 1920,
              height: 1080,
              backgroundColor: `rgba(255, 255, 255, ${pulseGlowOpacity})`,
              pointerEvents: "none",
            }}
          />
        )}
      </div>
    </AbsoluteFill>
  );
};

export default Part3Mold12ThreePillarsDiagram;
