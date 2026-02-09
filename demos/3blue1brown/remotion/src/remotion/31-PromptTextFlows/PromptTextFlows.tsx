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

  // Document opacity (spec: fade in, hold, then dim)
  const docOpacity = interpolate(
    frame,
    [BEATS.DOCUMENT_START, BEATS.DOCUMENT_PEAK, BEATS.DOCUMENT_FADE, BEATS.DOCUMENT_END],
    [0, 1, 1, 0.3],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Transform to code
  const transformProgress = interpolate(
    frame,
    [BEATS.TRANSFORM_START, BEATS.TRANSFORM_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Nozzle position
  const nozzleY = 280;
  const moldY = 680;

  // Individual text lines with their start frames
  const textLines = [
    { text: "Parse user IDs from untrusted input.", start: BEATS.LINE1_START },
    { text: "Return None on failure, never throw.", start: BEATS.LINE2_START },
    { text: "Handle unicode.", start: BEATS.LINE3_START },
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Prompt Document (spec: lines 121-126, 212-257) */}
      <div
        style={{
          position: "absolute",
          top: 120,
          left: "50%",
          transform: "translateX(-50%)",
          opacity: docOpacity,
        }}
      >
        <div
          style={{
            width: 180,
            background: "rgba(74, 144, 217, 0.1)",
            border: `2px solid ${COLORS.NOZZLE_BLUE}`,
            borderRadius: 8,
            padding: 12,
            boxShadow: `0 0 20px rgba(74, 144, 217, 0.3)`,
          }}
        >
          <div
            style={{
              fontSize: 12,
              color: COLORS.NOZZLE_BLUE,
              fontFamily: "JetBrains Mono, monospace",
              marginBottom: 8,
            }}
          >
            user_parser.prompt
          </div>
          <div
            style={{
              fontSize: 10,
              color: "#888",
              lineHeight: 1.4,
            }}
          >
            Parse user IDs...<br />
            Return None...<br />
            Handle unicode.
          </div>
        </div>
      </div>

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

      {/* Flowing text lines (spec: lines 127-136, 149-209) */}
      {textLines.map((line, i) => {
        const elapsed = frame - line.start;
        if (elapsed < 0) return null;

        // Text position (moves down from document to nozzle)
        const y = interpolate(
          elapsed,
          [0, 60],
          [200, nozzleY],
          { extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
        );

        // Text opacity (fades as it enters nozzle)
        const opacity = interpolate(
          elapsed,
          [0, 30, 60, 90],
          [0, 1, 1, 0],
          { extrapolateRight: "clamp" }
        );

        // Text scale (shrinks into nozzle)
        const scale = interpolate(
          elapsed,
          [40, 70],
          [1, 0.3],
          { extrapolateRight: "clamp" }
        );

        // Text blur (becomes fluid - spec: lines 184-190)
        const blur = interpolate(
          elapsed,
          [50, 70],
          [0, 5],
          { extrapolateRight: "clamp" }
        );

        return (
          <div
            key={i}
            style={{
              position: "absolute",
              left: "50%",
              top: y,
              transform: `translateX(-50%) scale(${scale})`,
              opacity,
              filter: `blur(${blur}px)`,
              color: COLORS.NOZZLE_BLUE,
              fontSize: 20,
              fontFamily: "JetBrains Mono, monospace",
              whiteSpace: "nowrap",
            }}
          >
            {line.text}
          </div>
        );
      })}

      {/* Mold cavity with fluid accumulation (spec: lines 138-143) */}
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
            position: "relative",
            overflow: "hidden",
          }}
        >
          {/* Fluid accumulation layer */}
          <div
            style={{
              position: "absolute",
              bottom: 0,
              left: 0,
              right: 0,
              height: `${interpolate(frame, [BEATS.TEXT_FLOW_START, BEATS.TRANSFORM_END], [0, 100], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })}%`,
              background: `linear-gradient(to bottom, rgba(74, 144, 217, 0.2), rgba(138, 156, 175, 0.4))`,
              transition: "height 0.3s ease-out",
            }}
          />

          {/* Transforming text to code */}
          <div
            style={{
              position: "absolute",
              top: "50%",
              left: "50%",
              transform: "translate(-50%, -50%)",
              width: "100%",
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
            }}
          >
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
