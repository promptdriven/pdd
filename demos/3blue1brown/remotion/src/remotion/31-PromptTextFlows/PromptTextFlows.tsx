import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, PromptTextFlowsPropsType } from "./constants";

export const PromptTextFlows: React.FC<PromptTextFlowsPropsType> = ({
  promptText,
}) => {
  const frame = useCurrentFrame();

  // Nozzle visibility
  const nozzleOpacity = interpolate(
    frame,
    [BEATS.NOZZLE_START, BEATS.NOZZLE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Text flow progress (0 to 1)
  const flowProgress = interpolate(
    frame,
    [BEATS.TEXT_FLOW_START, BEATS.TEXT_FLOW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Transform to code
  const transformProgress = interpolate(
    frame,
    [BEATS.TRANSFORM_START, BEATS.TRANSFORM_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Nozzle position
  const nozzleY = 180;
  const moldY = 600;

  // Characters that have flowed
  const visibleChars = Math.floor(flowProgress * promptText.length);

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Nozzle */}
      <div
        style={{
          position: "absolute",
          top: nozzleY,
          left: "50%",
          transform: "translateX(-50%)",
          opacity: nozzleOpacity,
        }}
      >
        <div
          style={{
            width: 200,
            height: 80,
            background: "rgba(74, 144, 217, 0.3)",
            border: `3px solid ${COLORS.NOZZLE_BLUE}`,
            borderRadius: "20px 20px 8px 8px",
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            boxShadow: `0 0 30px rgba(74, 144, 217, 0.4)`,
          }}
        >
          <span
            style={{
              fontSize: 16,
              color: COLORS.NOZZLE_BLUE,
              fontWeight: "bold",
            }}
          >
            PROMPT
          </span>
        </div>
      </div>

      {/* Flowing text */}
      <div
        style={{
          position: "absolute",
          top: nozzleY + 100,
          left: "50%",
          transform: "translateX(-50%)",
          width: 600,
          textAlign: "center",
        }}
      >
        {/* Text above the flow */}
        <div
          style={{
            fontSize: 20,
            fontFamily: "sans-serif",
            color: COLORS.NOZZLE_BLUE,
            opacity: nozzleOpacity,
            marginBottom: 20,
          }}
        >
          {promptText.slice(0, visibleChars)}
          <span style={{ opacity: 0.3 }}>{promptText.slice(visibleChars)}</span>
        </div>

        {/* Flow stream */}
        {flowProgress > 0 && (
          <svg width="40" height={moldY - nozzleY - 200} style={{ overflow: "visible" }}>
            <defs>
              <linearGradient id="flowGradient" x1="0%" y1="0%" x2="0%" y2="100%">
                <stop offset="0%" stopColor={COLORS.NOZZLE_BLUE} stopOpacity={0.8} />
                <stop offset="100%" stopColor={COLORS.CODE_GRAY} stopOpacity={0.6} />
              </linearGradient>
            </defs>
            <rect
              x={15}
              y={0}
              width={10}
              height={(moldY - nozzleY - 200) * flowProgress}
              fill="url(#flowGradient)"
              rx={5}
            />
            {/* Particles */}
            {[...Array(5)].map((_, i) => {
              const particleY = ((i * 50) + frame * 3) % (moldY - nozzleY - 200);
              if (particleY > (moldY - nozzleY - 200) * flowProgress) return null;
              return (
                <circle
                  key={i}
                  cx={20}
                  cy={particleY}
                  r={4}
                  fill={COLORS.NOZZLE_BLUE}
                  opacity={0.6}
                />
              );
            })}
          </svg>
        )}
      </div>

      {/* Mold cavity */}
      <div
        style={{
          position: "absolute",
          top: moldY,
          left: "50%",
          transform: "translateX(-50%)",
          opacity: nozzleOpacity,
        }}
      >
        <div
          style={{
            width: 500,
            height: 200,
            background: "rgba(138, 156, 175, 0.1)",
            border: `2px solid ${COLORS.CODE_GRAY}`,
            borderRadius: 8,
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            overflow: "hidden",
          }}
        >
          {/* Transforming text to code */}
          <pre
            style={{
              fontSize: 14,
              fontFamily: "JetBrains Mono, monospace",
              color: COLORS.CODE_GRAY,
              opacity: transformProgress,
              transform: `scale(${0.8 + 0.2 * transformProgress})`,
              margin: 0,
            }}
          >
            {`def parse_user_id(input_str):
    if not input_str:
        return None
    ...`}
          </pre>
        </div>

        {/* Label */}
        <div
          style={{
            textAlign: "center",
            marginTop: 16,
            fontSize: 14,
            color: COLORS.LABEL_GRAY,
          }}
        >
          Code takes shape from the prompt
        </div>
      </div>

      {/* Caption */}
      <div
        style={{
          position: "absolute",
          bottom: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: interpolate(frame, [BEATS.HOLD_START, BEATS.HOLD_START + 30], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
        }}
      >
        <div
          style={{
            fontSize: 20,
            color: COLORS.LABEL_WHITE,
            fontFamily: "sans-serif",
          }}
        >
          Intent flows through the prompt, transformed into code
        </div>
      </div>
    </AbsoluteFill>
  );
};
