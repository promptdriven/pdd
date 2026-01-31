import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, PROMPT_CONTENT, LongPromptPropsType } from "./constants";

interface PromptFileProps {
  filename: string;
  content: string;
  lineCount: number;
  opacity: number;
  scrollProgress: number;
}

const PromptFile: React.FC<PromptFileProps> = ({
  filename,
  content,
  lineCount,
  opacity,
  scrollProgress,
}) => {
  const lines = content.split("\n");
  const maxVisibleLines = 25;
  const totalScrollableLines = Math.max(0, lines.length - maxVisibleLines);
  const visibleStart = Math.floor(scrollProgress * totalScrollableLines);
  const visibleLines = lines.slice(visibleStart, visibleStart + maxVisibleLines);

  return (
    <div
      style={{
        position: "absolute",
        left: 150,
        top: 100,
        width: 1100,
        height: 850,
        opacity,
      }}
    >
      {/* File header */}
      <div
        style={{
          backgroundColor: COLORS.HEADER_BLUE,
          padding: "12px 20px",
          borderTopLeftRadius: 8,
          borderTopRightRadius: 8,
          display: "flex",
          alignItems: "center",
          justifyContent: "space-between",
        }}
      >
        <span
          style={{
            color: "white",
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 18,
            fontWeight: "bold",
          }}
        >
          {filename}
        </span>
        <span
          style={{
            color: "rgba(255, 255, 255, 0.7)",
            fontSize: 14,
          }}
        >
          {lineCount} lines
        </span>
      </div>

      {/* File content */}
      <div
        style={{
          backgroundColor: COLORS.CONTENT_BG,
          padding: 20,
          borderBottomLeftRadius: 8,
          borderBottomRightRadius: 8,
          height: 750,
          overflow: "hidden",
          position: "relative",
        }}
      >
        {visibleLines.map((line, i) => {
          const isHeader = line.startsWith("#");
          const isBullet = line.trim().startsWith("-");

          return (
            <div
              key={i}
              style={{
                fontFamily: "JetBrains Mono, monospace",
                fontSize: 14,
                color: isHeader
                  ? COLORS.HEADER_BLUE
                  : isBullet
                    ? COLORS.BULLET_ORANGE
                    : COLORS.TEXT_GRAY,
                marginBottom: 4,
                whiteSpace: "pre",
                fontWeight: isHeader ? "bold" : "normal",
              }}
            >
              {line}
            </div>
          );
        })}

        {/* Fade indicator at bottom */}
        <div
          style={{
            position: "absolute",
            bottom: 0,
            left: 0,
            right: 0,
            height: 80,
            background: `linear-gradient(transparent, ${COLORS.CONTENT_BG})`,
            pointerEvents: "none",
          }}
        />

        {/* Scroll indicator */}
        {scrollProgress > 0 && scrollProgress < 1 && (
          <div
            style={{
              position: "absolute",
              right: 10,
              top: 10,
              bottom: 90,
              width: 4,
              backgroundColor: "rgba(255, 255, 255, 0.1)",
              borderRadius: 2,
            }}
          >
            <div
              style={{
                position: "absolute",
                top: `${scrollProgress * 80}%`,
                width: "100%",
                height: "20%",
                backgroundColor: COLORS.HEADER_BLUE,
                borderRadius: 2,
                opacity: 0.6,
              }}
            />
          </div>
        )}
      </div>
    </div>
  );
};

interface TestWallsSmallProps {
  count: number;
  opacity: number;
  position: { x: number; y: number };
}

const TestWallsSmall: React.FC<TestWallsSmallProps> = ({
  count,
  opacity,
  position,
}) => {
  return (
    <div
      style={{
        position: "absolute",
        left: position.x,
        top: position.y,
        opacity,
      }}
    >
      {[...Array(count)].map((_, i) => (
        <div
          key={i}
          style={{
            width: 50,
            height: 70,
            backgroundColor: COLORS.WALLS_AMBER,
            borderRadius: 6,
            marginBottom: 20,
            boxShadow: `0 0 20px rgba(217, 148, 74, 0.4)`,
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
          }}
        >
          <span
            style={{
              fontSize: 10,
              color: "rgba(0, 0, 0, 0.5)",
              fontFamily: "JetBrains Mono, monospace",
            }}
          >
            test
          </span>
        </div>
      ))}

      {/* Label */}
      <div
        style={{
          marginTop: 10,
          color: "rgba(255, 255, 255, 0.5)",
          fontSize: 14,
          textAlign: "center",
        }}
      >
        {count} tests
      </div>
    </div>
  );
};

interface LineCountBadgeProps {
  count: number;
  opacity: number;
}

const LineCountBadge: React.FC<LineCountBadgeProps> = ({ count, opacity }) => {
  return (
    <div
      style={{
        position: "absolute",
        left: 1150,
        top: 140,
        opacity,
        backgroundColor: "rgba(74, 144, 217, 0.2)",
        border: `1px solid ${COLORS.HEADER_BLUE}`,
        borderRadius: 20,
        padding: "8px 16px",
        display: "flex",
        alignItems: "center",
        gap: 8,
      }}
    >
      <span
        style={{
          fontSize: 24,
          fontWeight: "bold",
          color: COLORS.HEADER_BLUE,
        }}
      >
        {count}
      </span>
      <span
        style={{
          fontSize: 14,
          color: COLORS.LABEL_GRAY,
        }}
      >
        lines
      </span>
    </div>
  );
};

export const LongPrompt: React.FC<LongPromptPropsType> = ({
  showTestWalls = true,
}) => {
  const frame = useCurrentFrame();

  // Container opacity (0-90 frames: 0-3s)
  const containerOpacity = interpolate(
    frame,
    [BEATS.CONTAINER_FADE_START, BEATS.CONTAINER_FADE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Scroll progress (90-270 frames: 3-9s)
  const scrollProgress = interpolate(
    frame,
    [BEATS.SCROLL_START, BEATS.SCROLL_END],
    [0, 0.6],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );

  // Test walls opacity (270-330 frames: 9-11s)
  const wallsOpacity = interpolate(
    frame,
    [BEATS.WALLS_FADE_START, BEATS.WALLS_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Count lines in prompt content
  const lineCount = PROMPT_CONTENT.split("\n").length;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Prompt file display */}
      <PromptFile
        filename="parser_v1.prompt"
        content={PROMPT_CONTENT}
        lineCount={lineCount}
        opacity={containerOpacity}
        scrollProgress={scrollProgress}
      />

      {/* Line count badge */}
      <LineCountBadge count={lineCount} opacity={containerOpacity} />

      {/* Few test walls */}
      {showTestWalls && (
        <TestWallsSmall
          count={3}
          opacity={wallsOpacity}
          position={{ x: 1450, y: 350 }}
        />
      )}

      {/* Caption at bottom */}
      {containerOpacity > 0.5 && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: interpolate(
              frame,
              [BEATS.WALLS_FADE_END, BEATS.WALLS_FADE_END + 30],
              [0, 1],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
          }}
        >
          <div
            style={{
              fontSize: 20,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
              fontStyle: "italic",
            }}
          >
            "With few tests, your prompt needs to specify everything."
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
