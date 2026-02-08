import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, OLD_CODE, NEW_CODE, CodeRegeneratesPropsType } from "./constants";

/** Terminal snippet overlay styled as a small terminal window. */
const TerminalOverlay: React.FC<{
  lines: Array<{ text: string; color?: string }>;
  opacity: number;
}> = ({ lines, opacity }) => {
  if (opacity <= 0) return null;
  return (
    <div
      style={{
        position: "absolute",
        bottom: 30,
        right: 30,
        width: 300,
        opacity,
      }}
    >
      <div
        style={{
          background: "#252535",
          border: "1px solid #444",
          borderRadius: 6,
          padding: "10px 14px",
          minHeight: 80,
        }}
      >
        {/* Terminal title bar dots */}
        <div style={{ display: "flex", gap: 5, marginBottom: 8 }}>
          <div style={{ width: 8, height: 8, borderRadius: "50%", background: "#E74C3C" }} />
          <div style={{ width: 8, height: 8, borderRadius: "50%", background: "#F1C40F" }} />
          <div style={{ width: 8, height: 8, borderRadius: "50%", background: "#2ECC71" }} />
        </div>
        {lines.map((line, i) => (
          <div
            key={i}
            style={{
              fontSize: 12,
              fontFamily: "JetBrains Mono, monospace",
              color: line.color || "#ccc",
              lineHeight: 1.6,
              whiteSpace: "pre",
            }}
          >
            {line.text}
          </div>
        ))}
      </div>
    </div>
  );
};

export const CodeRegenerates: React.FC<CodeRegeneratesPropsType> = ({
  showTransition = true,
}) => {
  const frame = useCurrentFrame();

  // Old code visibility
  const oldCodeOpacity = interpolate(
    frame,
    [BEATS.OLD_CODE_START, BEATS.OLD_CODE_END, BEATS.DISSOLVE_START, BEATS.DISSOLVE_END],
    [0, 1, 1, 0],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Dissolve effect (particle scatter simulation via opacity flicker)
  const dissolveProgress = interpolate(
    frame,
    [BEATS.DISSOLVE_START, BEATS.DISSOLVE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // New code regeneration
  const newCodeOpacity = interpolate(
    frame,
    [BEATS.REGENERATE_START, BEATS.REGENERATE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // New code glow
  const newCodeGlow = interpolate(
    frame,
    [BEATS.NEW_CODE_GLOW_START, BEATS.NEW_CODE_GLOW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Checkmark
  const checkmarkOpacity = interpolate(
    frame,
    [BEATS.CHECKMARK_START, BEATS.CHECKMARK_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Dissolve blur effect
  const dissolveBlur = dissolveProgress * 10;

  // Terminal overlay opacity -- appears when dissolve starts
  const terminalOpacity = interpolate(
    frame,
    [BEATS.DISSOLVE_START, BEATS.DISSOLVE_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Terminal lines (progressively revealed)
  const terminalLines: Array<{ text: string; color?: string }> = [
    { text: "$ pdd fix user_parser", color: "#4A90D9" },
  ];
  if (frame >= BEATS.REGENERATE_START) {
    terminalLines.push({ text: "Regenerating code...", color: "#ccc" });
  }
  if (frame >= BEATS.CHECKMARK_START) {
    terminalLines.push({ text: "All tests passing \u2713", color: "#4CAF50" });
  }

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Old code (dissolving) */}
      {oldCodeOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
            opacity: oldCodeOpacity,
            filter: dissolveProgress > 0 ? `blur(${dissolveBlur}px)` : "none",
          }}
        >
          <div
            style={{
              background: "#1E1E2E",
              padding: 24,
              borderRadius: 12,
              border: "1px solid #E74C3C",
              boxShadow: dissolveProgress > 0
                ? `0 0 ${30 * dissolveProgress}px ${COLORS.DISSOLVE_ORANGE}`
                : "none",
            }}
          >
            <div
              style={{
                fontSize: 12,
                color: "#E74C3C",
                marginBottom: 12,
                fontFamily: "sans-serif",
              }}
            >
              OLD CODE (with bug)
            </div>
            <pre
              style={{
                fontSize: 14,
                fontFamily: "JetBrains Mono, monospace",
                color: COLORS.CODE_GRAY,
                margin: 0,
                lineHeight: 1.6,
              }}
            >
              {OLD_CODE}
            </pre>
          </div>
        </div>
      )}

      {/* Dissolve particles (visual effect) */}
      {dissolveProgress > 0 && dissolveProgress < 1 && showTransition && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
          }}
        >
          {[...Array(20)].map((_, i) => {
            const angle = (i / 20) * Math.PI * 2;
            const distance = 50 + dissolveProgress * 200;
            const x = Math.cos(angle) * distance;
            const y = Math.sin(angle) * distance;
            return (
              <div
                key={i}
                style={{
                  position: "absolute",
                  width: 8,
                  height: 8,
                  borderRadius: "50%",
                  background: COLORS.DISSOLVE_ORANGE,
                  transform: `translate(${x}px, ${y}px)`,
                  opacity: 1 - dissolveProgress,
                }}
              />
            );
          })}
        </div>
      )}

      {/* New code (regenerating) */}
      {newCodeOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%)",
            opacity: newCodeOpacity,
          }}
        >
          <div
            style={{
              background: "#1E1E2E",
              padding: 24,
              borderRadius: 12,
              border: `1px solid ${newCodeGlow > 0 ? COLORS.SUCCESS_GREEN : "#333"}`,
              boxShadow: newCodeGlow > 0
                ? `0 0 ${30 * newCodeGlow}px ${COLORS.SUCCESS_GREEN}`
                : "none",
            }}
          >
            <div
              style={{
                fontSize: 12,
                color: COLORS.SUCCESS_GREEN,
                marginBottom: 12,
                fontFamily: "sans-serif",
              }}
            >
              NEW CODE (fixed)
            </div>
            <pre
              style={{
                fontSize: 14,
                fontFamily: "JetBrains Mono, monospace",
                color: COLORS.CODE_GRAY,
                margin: 0,
                lineHeight: 1.6,
              }}
            >
              {NEW_CODE}
            </pre>
          </div>
        </div>
      )}

      {/* Checkmark */}
      {checkmarkOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: 180,
            left: "50%",
            transform: "translateX(-50%)",
            fontSize: 48,
            color: COLORS.SUCCESS_GREEN,
            opacity: checkmarkOpacity,
            textShadow: `0 0 20px ${COLORS.SUCCESS_GREEN}`,
          }}
        >
          {"\u2713"} All tests pass
        </div>
      )}

      {/* Terminal snippet overlay */}
      <TerminalOverlay lines={terminalLines} opacity={terminalOpacity} />

      {/* Caption */}
      <div
        style={{
          position: "absolute",
          bottom: 80,
          left: 0,
          right: 340,
          textAlign: "center",
          opacity: interpolate(frame, [BEATS.HOLD_START, BEATS.HOLD_START + 30], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
        }}
      >
        <div
          style={{
            fontSize: 22,
            color: COLORS.LABEL_WHITE,
            fontFamily: "sans-serif",
          }}
        >
          The code regenerates to fit the updated mold.
        </div>
      </div>
    </AbsoluteFill>
  );
};
