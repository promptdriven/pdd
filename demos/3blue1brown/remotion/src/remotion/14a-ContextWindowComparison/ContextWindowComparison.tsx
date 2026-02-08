import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  spring,
  useCurrentFrame,
  useVideoConfig,
} from "remotion";
import {
  COLORS,
  BEATS,
  WINDOW,
  RIGHT_BLOCKS,
  CODE_PATTERNS,
  TOKEN_COUNTS,
  ContextWindowComparisonPropsType,
} from "./constants";

/**
 * ContextWindowComparison: Side-by-side comparison of "Agentic Patching"
 * (15,000 tokens, cluttered) vs. "PDD Regeneration" (2,300 tokens, clean).
 *
 * LEFT: Dense code with red "irrelevant" overlays, tiny green "relevant" sliver
 * RIGHT: Clean blocks (Prompt, Tests, Grounding) with "Room to think" empty space
 */
export const ContextWindowComparison: React.FC<ContextWindowComparisonPropsType> = ({
  showKnowledgeIndicator = true,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // === ANIMATION PROGRESS VALUES ===

  // Divider draw
  const dividerProgress = interpolate(
    frame,
    [BEATS.ESTABLISH_START, BEATS.ESTABLISH_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Labels fade in
  const labelOpacity = interpolate(
    frame,
    [BEATS.ESTABLISH_START + 10, BEATS.ESTABLISH_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Window frames spring in
  const windowScale = spring({
    frame: Math.max(0, frame - BEATS.FRAMES_START),
    fps,
    config: { damping: 15, stiffness: 120 },
  });

  // Left code fill progress
  const leftFillProgress = interpolate(
    frame,
    [BEATS.LEFT_FILL_START, BEATS.LEFT_FILL_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Right blocks slide in
  const rightBlockDelay = (index: number) => BEATS.RIGHT_FILL_START + index * 15;
  const getRightBlockProgress = (index: number) => {
    return interpolate(
      frame,
      [rightBlockDelay(index), rightBlockDelay(index) + 30],
      [0, 1],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      }
    );
  };

  // "Room to think" text
  const roomToThinkOpacity = interpolate(
    frame,
    [BEATS.RIGHT_FILL_START + 60, BEATS.RIGHT_FILL_START + 90],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Token counters
  const leftCounterValue = Math.round(
    interpolate(
      frame,
      [BEATS.COUNTER_START, BEATS.COUNTER_START + 60],
      [0, TOKEN_COUNTS.left],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      }
    )
  );

  const rightCounterValue = Math.round(
    interpolate(
      frame,
      [BEATS.COUNTER_START + 10, BEATS.COUNTER_START + 55],
      [0, TOKEN_COUNTS.right],
      {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.quad),
      }
    )
  );

  // Badge pop in
  const badgeScale = spring({
    frame: Math.max(0, frame - BEATS.BADGE_APPEAR),
    fps,
    config: { damping: 12, stiffness: 150 },
  });

  // Knowledge indicator
  const knowledgeOpacity = interpolate(
    frame,
    [BEATS.KNOWLEDGE_START, BEATS.KNOWLEDGE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Hold phase idle pulses
  const leftPulse =
    frame >= BEATS.HOLD_START
      ? 0.98 + 0.02 * Math.sin((frame - BEATS.HOLD_START) * 0.1)
      : 1;
  const rightShimmer =
    frame >= BEATS.HOLD_START
      ? 0.98 + 0.02 * Math.sin((frame - BEATS.HOLD_START) * 0.08 + 1)
      : 1;

  // Left border red glow after fill
  const leftGlowOpacity =
    frame >= BEATS.LEFT_FILL_END
      ? 0.2 + 0.1 * Math.sin((frame - BEATS.LEFT_FILL_END) * 0.15)
      : 0;

  // === HELPER: Code lines for left panel ===
  const visibleLineCount = Math.floor(leftFillProgress * CODE_PATTERNS.length);
  const codeLines = CODE_PATTERNS.slice(0, visibleLineCount);

  // Calculate highlight zones
  const irrelevantZones = [
    { startLine: 0, endLine: Math.floor(visibleLineCount * 0.42) },
    { startLine: Math.floor(visibleLineCount * 0.48), endLine: visibleLineCount },
  ];
  const relevantZone = {
    startLine: Math.floor(visibleLineCount * 0.42),
    endLine: Math.floor(visibleLineCount * 0.48),
  };

  // Window content area dimensions
  const contentHeight = WINDOW.height - WINDOW.chromeHeight;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* === VERTICAL DIVIDER === */}
      {dividerProgress > 0 && (
        <div
          style={{
            position: "absolute",
            left: WINDOW.dividerX,
            top: 0,
            width: 1,
            height: `${dividerProgress * 100}%`,
            backgroundColor: COLORS.DIVIDER,
            opacity: 0.5,
          }}
        />
      )}

      {/* === PANEL LABELS === */}
      {labelOpacity > 0 && (
        <>
          {/* Left label */}
          <div
            style={{
              position: "absolute",
              left: WINDOW.leftCenterX,
              top: 50,
              transform: "translateX(-50%)",
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 28,
              fontWeight: 600,
              color: COLORS.LABEL_WHITE,
              opacity: labelOpacity,
              textShadow: `0 0 20px ${COLORS.LEFT_COUNTER}40`,
            }}
          >
            Agentic Patching
          </div>

          {/* Right label */}
          <div
            style={{
              position: "absolute",
              left: WINDOW.rightCenterX,
              top: 50,
              transform: "translateX(-50%)",
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 28,
              fontWeight: 600,
              color: COLORS.LABEL_WHITE,
              opacity: labelOpacity,
              textShadow: `0 0 20px ${COLORS.RIGHT_COUNTER}40`,
            }}
          >
            PDD Regeneration
          </div>
        </>
      )}

      {/* === LEFT CONTEXT WINDOW === */}
      <div
        style={{
          position: "absolute",
          left: WINDOW.leftCenterX - WINDOW.width / 2,
          top: WINDOW.centerY - WINDOW.height / 2,
          width: WINDOW.width,
          height: WINDOW.height,
          transform: `scale(${windowScale * leftPulse})`,
          transformOrigin: "center center",
          borderRadius: WINDOW.borderRadius,
          border: `1px solid ${COLORS.WINDOW_BORDER}`,
          backgroundColor: COLORS.WINDOW_BG,
          overflow: "hidden",
          boxShadow: leftGlowOpacity > 0
            ? `0 0 20px rgba(217, 74, 74, ${leftGlowOpacity})`
            : "none",
        }}
      >
        {/* Chrome bar */}
        <div
          style={{
            height: WINDOW.chromeHeight,
            backgroundColor: COLORS.CHROME_BG,
            display: "flex",
            alignItems: "center",
            paddingLeft: 10,
            gap: 6,
          }}
        >
          <div style={{ width: 10, height: 10, borderRadius: "50%", backgroundColor: COLORS.CHROME_DOT_RED }} />
          <div style={{ width: 10, height: 10, borderRadius: "50%", backgroundColor: COLORS.CHROME_DOT_YELLOW }} />
          <div style={{ width: 10, height: 10, borderRadius: "50%", backgroundColor: COLORS.CHROME_DOT_GREEN }} />
        </div>

        {/* Code content */}
        <div
          style={{
            position: "relative",
            height: contentHeight,
            overflow: "hidden",
            padding: "6px 10px",
          }}
        >
          {/* Code lines */}
          {codeLines.map((line, i) => {
            const isIrrelevant = irrelevantZones.some(
              (z) => i >= z.startLine && i < z.endLine
            );
            const isRelevant =
              i >= relevantZone.startLine && i < relevantZone.endLine;

            return (
              <div
                key={`code-${i}`}
                style={{
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: 10,
                  lineHeight: "14px",
                  color: COLORS.CODE_TEXT,
                  whiteSpace: "pre",
                  backgroundColor: isRelevant
                    ? COLORS.RELEVANT_GREEN
                    : isIrrelevant
                      ? COLORS.IRRELEVANT_RED
                      : "transparent",
                  position: "relative",
                }}
              >
                {line || "\u00A0"}
              </div>
            );
          })}

          {/* IRRELEVANT watermarks */}
          {leftFillProgress > 0.5 && (
            <>
              <div
                style={{
                  position: "absolute",
                  top: "15%",
                  left: "50%",
                  transform: "translateX(-50%) rotate(-10deg)",
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 14,
                  fontWeight: 700,
                  color: COLORS.IRRELEVANT_LABEL,
                  letterSpacing: 4,
                  opacity: interpolate(leftFillProgress, [0.5, 0.8], [0, 0.6], {
                    extrapolateLeft: "clamp",
                    extrapolateRight: "clamp",
                  }),
                  pointerEvents: "none",
                }}
              >
                IRRELEVANT
              </div>
              <div
                style={{
                  position: "absolute",
                  top: "70%",
                  left: "40%",
                  transform: "translateX(-50%) rotate(5deg)",
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 14,
                  fontWeight: 700,
                  color: COLORS.IRRELEVANT_LABEL,
                  letterSpacing: 4,
                  opacity: interpolate(leftFillProgress, [0.7, 1], [0, 0.5], {
                    extrapolateLeft: "clamp",
                    extrapolateRight: "clamp",
                  }),
                  pointerEvents: "none",
                }}
              >
                IRRELEVANT
              </div>
            </>
          )}
        </div>
      </div>

      {/* === RIGHT CONTEXT WINDOW === */}
      <div
        style={{
          position: "absolute",
          left: WINDOW.rightCenterX - WINDOW.width / 2,
          top: WINDOW.centerY - WINDOW.height / 2,
          width: WINDOW.width,
          height: WINDOW.height,
          transform: `scale(${windowScale * rightShimmer})`,
          transformOrigin: "center center",
          borderRadius: WINDOW.borderRadius,
          border: `1px solid ${COLORS.WINDOW_BORDER}`,
          backgroundColor: COLORS.WINDOW_BG,
          overflow: "hidden",
        }}
      >
        {/* Chrome bar */}
        <div
          style={{
            height: WINDOW.chromeHeight,
            backgroundColor: COLORS.CHROME_BG,
            display: "flex",
            alignItems: "center",
            paddingLeft: 10,
            gap: 6,
          }}
        >
          <div style={{ width: 10, height: 10, borderRadius: "50%", backgroundColor: COLORS.CHROME_DOT_RED }} />
          <div style={{ width: 10, height: 10, borderRadius: "50%", backgroundColor: COLORS.CHROME_DOT_YELLOW }} />
          <div style={{ width: 10, height: 10, borderRadius: "50%", backgroundColor: COLORS.CHROME_DOT_GREEN }} />
        </div>

        {/* Clean blocks content */}
        <div
          style={{
            position: "relative",
            height: contentHeight,
            padding: "16px 20px",
            display: "flex",
            flexDirection: "column",
            gap: 12,
          }}
        >
          {/* Prompt block */}
          {getRightBlockProgress(0) > 0 && (
            <div
              style={{
                height: `${RIGHT_BLOCKS.promptHeight * 100}%`,
                backgroundColor: COLORS.PROMPT_BLUE,
                borderRadius: 6,
                display: "flex",
                alignItems: "center",
                justifyContent: "center",
                opacity: getRightBlockProgress(0),
                transform: `translateX(${(1 - getRightBlockProgress(0)) * 40}px)`,
              }}
            >
              <span
                style={{
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 14,
                  fontWeight: 500,
                  color: COLORS.LABEL_WHITE,
                }}
              >
                Prompt (300 tokens)
              </span>
            </div>
          )}

          {/* Tests block */}
          {getRightBlockProgress(1) > 0 && (
            <div
              style={{
                height: `${RIGHT_BLOCKS.testsHeight * 100}%`,
                backgroundColor: COLORS.TESTS_AMBER,
                borderRadius: 6,
                display: "flex",
                alignItems: "center",
                justifyContent: "center",
                opacity: getRightBlockProgress(1),
                transform: `translateX(${(1 - getRightBlockProgress(1)) * 40}px)`,
              }}
            >
              <span
                style={{
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 14,
                  fontWeight: 500,
                  color: COLORS.LABEL_WHITE,
                }}
              >
                Tests (2,000 tokens)
              </span>
            </div>
          )}

          {/* Grounding Example block */}
          {getRightBlockProgress(2) > 0 && (
            <div
              style={{
                height: `${RIGHT_BLOCKS.groundingHeight * 100}%`,
                backgroundColor: COLORS.GROUNDING_GREEN,
                borderRadius: 6,
                display: "flex",
                alignItems: "center",
                justifyContent: "center",
                opacity: getRightBlockProgress(2),
                transform: `translateX(${(1 - getRightBlockProgress(2)) * 40}px)`,
              }}
            >
              <span
                style={{
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 14,
                  fontWeight: 500,
                  color: COLORS.LABEL_WHITE,
                }}
              >
                Grounding Example
              </span>
            </div>
          )}

          {/* Empty space - "Room to think" */}
          <div
            style={{
              flex: 1,
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
            }}
          >
            {roomToThinkOpacity > 0 && (
              <span
                style={{
                  fontFamily: "Inter, system-ui, sans-serif",
                  fontSize: 16,
                  fontStyle: "italic",
                  color: COLORS.ROOM_TO_THINK,
                  opacity: roomToThinkOpacity,
                }}
              >
                Room to think
              </span>
            )}
          </div>
        </div>
      </div>

      {/* === TOKEN COUNTERS === */}
      {frame >= BEATS.COUNTER_START && (
        <>
          {/* Left counter */}
          <div
            style={{
              position: "absolute",
              left: WINDOW.leftCenterX,
              top: WINDOW.centerY + WINDOW.height / 2 + 30,
              transform: "translateX(-50%)",
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 20,
              fontWeight: 600,
              color: interpolate(
                leftCounterValue,
                [0, TOKEN_COUNTS.left],
                [1, 1],
                { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
              ) > 0
                ? COLORS.LEFT_COUNTER
                : COLORS.LABEL_WHITE,
              textShadow: `0 0 10px ${COLORS.LEFT_COUNTER}40`,
            }}
          >
            {leftCounterValue.toLocaleString()} tokens
          </div>

          {/* Right counter */}
          <div
            style={{
              position: "absolute",
              left: WINDOW.rightCenterX,
              top: WINDOW.centerY + WINDOW.height / 2 + 30,
              transform: "translateX(-50%)",
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 20,
              fontWeight: 600,
              color: COLORS.RIGHT_COUNTER,
              textShadow: `0 0 10px ${COLORS.RIGHT_COUNTER}40`,
            }}
          >
            {rightCounterValue.toLocaleString()} tokens
          </div>
        </>
      )}

      {/* === 6.5x FEWER TOKENS BADGE === */}
      {frame >= BEATS.BADGE_APPEAR && (
        <div
          style={{
            position: "absolute",
            left: WINDOW.dividerX,
            top: WINDOW.centerY + WINDOW.height / 2 + 25,
            transform: `translateX(-50%) scale(${badgeScale})`,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 16,
            fontWeight: 700,
            color: COLORS.BADGE_WHITE,
            backgroundColor: "rgba(74, 144, 217, 0.25)",
            border: `1px solid ${COLORS.RIGHT_COUNTER}`,
            borderRadius: 20,
            padding: "6px 18px",
            whiteSpace: "nowrap",
            textShadow: "0 0 8px rgba(255,255,255,0.3)",
          }}
        >
          6.5x fewer tokens
        </div>
      )}

      {/* === KNOWLEDGE INDICATOR === */}
      {showKnowledgeIndicator && knowledgeOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: "50%",
            top: WINDOW.centerY + WINDOW.height / 2 + 80,
            transform: "translateX(-50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 18,
            fontWeight: 500,
            color: COLORS.KNOWLEDGE_GREEN,
            opacity: knowledgeOpacity,
            textShadow: `0 0 12px ${COLORS.KNOWLEDGE_GREEN}40`,
          }}
        >
          10x more system knowledge
        </div>
      )}
    </AbsoluteFill>
  );
};
