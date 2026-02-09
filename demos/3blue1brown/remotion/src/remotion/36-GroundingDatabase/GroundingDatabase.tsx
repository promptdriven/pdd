import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, GroundingDatabasePropsType } from "./constants";

// Helper function to calculate point on quadratic bezier curve
// Path: M0,100 Q150,100 200,200 T400,300
// This uses quadratic bezier for first segment and smooth continuation (T) for second
const getPointOnPath = (t: number): { x: number; y: number } => {
  // Clamp t to [0, 1]
  t = Math.max(0, Math.min(1, t));

  // The path has two segments: Q150,100 200,200 and T400,300
  // Split at midpoint (t=0.5)
  if (t <= 0.5) {
    // First quadratic bezier: start(0,100), control(150,100), end(200,200)
    const localT = t * 2; // Scale to [0,1] for this segment
    const p0 = { x: 0, y: 100 };
    const p1 = { x: 150, y: 100 };
    const p2 = { x: 200, y: 200 };

    const x = Math.pow(1 - localT, 2) * p0.x + 2 * (1 - localT) * localT * p1.x + Math.pow(localT, 2) * p2.x;
    const y = Math.pow(1 - localT, 2) * p0.y + 2 * (1 - localT) * localT * p1.y + Math.pow(localT, 2) * p2.y;

    return { x, y };
  } else {
    // Second quadratic bezier (T continuation): start(200,200), control(250,300), end(400,300)
    // The control point is reflected from previous
    const localT = (t - 0.5) * 2; // Scale to [0,1] for this segment
    const p0 = { x: 200, y: 200 };
    const p1 = { x: 250, y: 300 }; // Reflected control point
    const p2 = { x: 400, y: 300 };

    const x = Math.pow(1 - localT, 2) * p0.x + 2 * (1 - localT) * localT * p1.x + Math.pow(localT, 2) * p2.x;
    const y = Math.pow(1 - localT, 2) * p0.y + 2 * (1 - localT) * localT * p1.y + Math.pow(localT, 2) * p2.y;

    return { x, y };
  }
};

export const GroundingDatabase: React.FC<GroundingDatabasePropsType> = ({
  showFeedbackLoop = true,
}) => {
  const frame = useCurrentFrame();

  // Success state visibility
  const successOpacity = interpolate(
    frame,
    [BEATS.SUCCESS_START, BEATS.SUCCESS_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Data pair highlight
  const dataPairGlow = interpolate(
    frame,
    [BEATS.DATA_HIGHLIGHT_START, BEATS.DATA_HIGHLIGHT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Flow arrow progress
  const flowProgress = interpolate(
    frame,
    [BEATS.FLOW_START, BEATS.FLOW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Database appearance
  const dbOpacity = interpolate(
    frame,
    [BEATS.DB_APPEAR_START, BEATS.DB_APPEAR_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Database pulse - adjusted to spec timing and scale
  const dbPulse = interpolate(
    frame,
    [BEATS.DB_PULSE_START, BEATS.DB_PULSE_START + 20, BEATS.DB_PULSE_START + 60],
    [1, 1.1, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.5)) }
  );

  // "Learning from success..." message opacity
  const learningMessageOpacity = interpolate(
    frame,
    [BEATS.DATA_HIGHLIGHT_START, BEATS.DATA_HIGHLIGHT_START + 30, BEATS.DATA_HIGHLIGHT_END - 30, BEATS.DATA_HIGHLIGHT_END],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Feedback arrow
  const feedbackOpacity = interpolate(
    frame,
    [BEATS.FEEDBACK_START, BEATS.FEEDBACK_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Quote
  const quoteOpacity = interpolate(
    frame,
    [BEATS.QUOTE_START, BEATS.QUOTE_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Positions
  const codeBlockX = 300;
  const databaseX = 1400;
  const centerY = 400;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Successful code generation */}
      <div
        style={{
          position: "absolute",
          left: codeBlockX,
          top: centerY,
          transform: "translate(-50%, -50%)",
          opacity: successOpacity,
        }}
      >
        <div
          style={{
            background: "#1E1E2E",
            padding: 20,
            borderRadius: 12,
            border: `2px solid ${dataPairGlow > 0 ? COLORS.GROUNDING_GREEN : "#333"}`,
            boxShadow: dataPairGlow > 0 ? `0 0 20px rgba(90, 170, 110, 0.4)` : "none",
          }}
        >
          <div
            style={{
              fontSize: 12,
              color: COLORS.SUCCESS_GREEN,
              marginBottom: 12,
            }}
          >
            ✓ pdd fix succeeded
          </div>
          <pre
            style={{
              fontSize: 12,
              fontFamily: "JetBrains Mono, monospace",
              color: COLORS.CODE_GRAY,
              margin: 0,
              lineHeight: 1.4,
            }}
          >
            {`def parse_user_id(input_str):
    if not input_str or not input_str.strip():
        return None
    cleaned = input_str.strip()
    if not cleaned.isalnum():
        return None
    return cleaned`}
          </pre>
        </div>

        {/* Data pair label */}
        {dataPairGlow > 0 && (
          <div
            style={{
              marginTop: 16,
              textAlign: "center",
              fontSize: 14,
              color: COLORS.GROUNDING_GREEN,
              opacity: dataPairGlow,
            }}
          >
            (prompt, code) pair
          </div>
        )}
      </div>

      {/* "Learning from success..." message */}
      {learningMessageOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: codeBlockX,
            top: centerY + 140,
            transform: "translateX(-50%)",
            opacity: learningMessageOpacity,
            fontSize: 16,
            color: COLORS.GROUNDING_GREEN,
            fontStyle: "italic",
          }}
        >
          Learning from success...
        </div>
      )}

      {/* Flow arrow with particles */}
      <svg
        width="600"
        height="400"
        style={{
          position: "absolute",
          left: codeBlockX + 150,
          top: centerY - 100,
        }}
      >
        <defs>
          <marker
            id="arrowhead"
            markerWidth="10"
            markerHeight="7"
            refX="9"
            refY="3.5"
            orient="auto"
          >
            <polygon points="0 0, 10 3.5, 0 7" fill={COLORS.GROUNDING_GREEN} />
          </marker>
        </defs>

        {/* Arrow path - curved as per spec */}
        <path
          d="M0,100 Q150,100 200,200 T400,300"
          fill="none"
          stroke={COLORS.GROUNDING_GREEN}
          strokeWidth={3}
          strokeDasharray={600}
          strokeDashoffset={600 * (1 - flowProgress)}
          opacity={flowProgress > 0 ? 1 : 0}
          markerEnd={flowProgress > 0.9 ? "url(#arrowhead)" : ""}
        />

        {/* Particles - 5 particles following bezier path */}
        {flowProgress > 0 && (
          <>
            {[0.1, 0.3, 0.5, 0.7, 0.9].map((offset, i) => {
              const particleProgress = flowProgress - offset;
              if (particleProgress <= 0) return null;

              // Get position along the bezier curve
              const pos = getPointOnPath(Math.min(particleProgress / (1 - offset), 1));

              // Fade out particles near the end
              const opacity = particleProgress < 0.9 ? 0.8 : Math.max(0, (1 - particleProgress) * 8);

              return (
                <circle
                  key={i}
                  cx={pos.x}
                  cy={pos.y}
                  r={6}
                  fill={COLORS.GROUNDING_GREEN}
                  opacity={opacity}
                />
              );
            })}
          </>
        )}
      </svg>

      {/* Database icon */}
      <div
        style={{
          position: "absolute",
          left: databaseX,
          top: centerY,
          transform: `translate(-50%, -50%) scale(${dbPulse})`,
          opacity: dbOpacity,
          textAlign: "center",
        }}
      >
        <div
          style={{
            width: 140,
            height: 120,
            background: "rgba(90, 170, 110, 0.15)",
            border: `3px solid ${COLORS.GROUNDING_GREEN}`,
            borderRadius: "20px 20px 12px 12px",
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            boxShadow: `0 0 ${30 * dbPulse}px rgba(90, 170, 110, 0.3)`,
          }}
        >
          <span style={{ fontSize: 48 }}>☁️</span>
        </div>
        <div
          style={{
            marginTop: 16,
            fontSize: 16,
            color: COLORS.GROUNDING_GREEN,
            fontWeight: "bold",
          }}
        >
          Grounding Database
        </div>
      </div>

      {/* Feedback arrow */}
      {showFeedbackLoop && feedbackOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: databaseX - 100,
            top: centerY + 120,
            opacity: feedbackOpacity,
          }}
        >
          <svg width="200" height="100">
            <path
              d="M150,10 C100,10 50,50 50,80"
              fill="none"
              stroke={COLORS.GROUNDING_GREEN}
              strokeWidth={2}
              strokeDasharray="6 4"
            />
            <polygon
              points="50,80 40,65 60,65"
              fill={COLORS.GROUNDING_GREEN}
            />
          </svg>
          <div
            style={{
              position: "absolute",
              left: -120,
              top: 60,
              fontSize: 14,
              color: COLORS.LABEL_GRAY,
              width: 150,
            }}
          >
            Informs future generations
          </div>
        </div>
      )}

      {/* Quote */}
      {quoteOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 80,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: quoteOpacity,
          }}
        >
          <div
            style={{
              fontSize: 22,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
              fontStyle: "italic",
            }}
          >
            "Your style. Your patterns. Your team's conventions."
          </div>
        </div>
      )}

      {/* Title */}
      <div
        style={{
          position: "absolute",
          top: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: successOpacity,
        }}
      >
        <span
          style={{
            fontSize: 24,
            fontFamily: "sans-serif",
            color: COLORS.GROUNDING_GREEN,
            fontWeight: "bold",
          }}
        >
          The Feedback Loop
        </span>
      </div>
    </AbsoluteFill>
  );
};
