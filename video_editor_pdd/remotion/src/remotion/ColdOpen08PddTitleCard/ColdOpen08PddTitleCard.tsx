import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  useVideoConfig,
  Easing,
  staticFile,
  OffthreadVideo,
} from "remotion";

// ── Constants (inlined to avoid cross-file imports) ───────────
const BG_COLOR = "#0A1628";
const BG_GRADIENT_TOP = "#0D1B2A";
const BG_GRADIENT_BOTTOM = "#060E1A";
const ACCENT_BLUE = "#3B82F6";
const ACCENT_CYAN = "#06B6D4";
const ACCENT_GREEN = "#22C55E";
const TEXT_WHITE = "#FFFFFF";
const TEXT_DIM = "#94A3B8";
const GLOW_BLUE = "rgba(59, 130, 246, 0.35)";
const GLOW_CYAN = "rgba(6, 182, 212, 0.25)";
const GRID_LINE_COLOR = "rgba(59, 130, 246, 0.12)";
const DIVIDER_COLOR = "rgba(59, 130, 246, 0.75)";
const DIVIDER_THICKNESS = 3;

const TITLE_FONT_SIZE = 96;
const SUBTITLE_FONT_SIZE = 32;
const LABEL_FONT_SIZE = 22;

const CANVAS_WIDTH = 1920;
const CANVAS_HEIGHT = 1080;

const GRID_FADE_IN_END = 15;
const TITLE_ENTER_START = 0;
const TITLE_ENTER_END = 20;
const DIVIDER_DRAW_START = 12;
const DIVIDER_DRAW_END = 28;
const SUBTITLE_ENTER_START = 18;
const SUBTITLE_ENTER_END = 34;
const PARTICLE_COUNT = 24;

// ── Default props ─────────────────────────────────────────────
export const defaultColdOpen08PddTitleCardProps = {};

// ── Inline Sub-Components ─────────────────────────────────────

/** Background grid with floating particles */
const AnimatedGridInline: React.FC<{
  width: number;
  height: number;
  frame: number;
}> = ({ width, height, frame }) => {
  const gridOpacity = interpolate(frame, [0, GRID_FADE_IN_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(3)),
  });

  const gridSpacing = 80;
  const verticalLines = Math.ceil(width / gridSpacing);
  const horizontalLines = Math.ceil(height / gridSpacing);

  const particles = React.useMemo(() => {
    return Array.from({ length: PARTICLE_COUNT }, (_, i) => {
      const seed1 = ((i * 7919 + 104729) % 1000) / 1000;
      const seed2 = ((i * 6271 + 73856) % 1000) / 1000;
      const seed3 = ((i * 4517 + 38447) % 1000) / 1000;
      return {
        x: seed1 * width,
        y: seed2 * height,
        size: 2 + seed3 * 3,
        speed: 0.3 + seed3 * 0.7,
        phase: seed1 * Math.PI * 2,
        useSecondary: i % 3 === 0,
      };
    });
  }, [width, height]);

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width,
        height,
        opacity: gridOpacity,
        overflow: "hidden",
      }}
    >
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {Array.from({ length: verticalLines + 1 }, (_, i) => (
          <line
            key={`v-${i}`}
            x1={i * gridSpacing}
            y1={0}
            x2={i * gridSpacing}
            y2={height}
            stroke={GRID_LINE_COLOR}
            strokeWidth={1}
          />
        ))}
        {Array.from({ length: horizontalLines + 1 }, (_, i) => (
          <line
            key={`h-${i}`}
            x1={0}
            y1={i * gridSpacing}
            x2={width}
            y2={i * gridSpacing}
            stroke={GRID_LINE_COLOR}
            strokeWidth={1}
          />
        ))}
      </svg>

      {particles.map((p, i) => {
        const yOffset = Math.sin(frame * 0.02 * p.speed + p.phase) * 30;
        const xOffset = Math.cos(frame * 0.015 * p.speed + p.phase) * 20;
        const particleOpacity = interpolate(
          Math.sin(frame * 0.03 + p.phase),
          [-1, 1],
          [0.15, 0.6],
        );
        return (
          <div
            key={i}
            style={{
              position: "absolute",
              left: p.x + xOffset,
              top: p.y + yOffset,
              width: p.size,
              height: p.size,
              borderRadius: "50%",
              backgroundColor: p.useSecondary ? ACCENT_GREEN : ACCENT_CYAN,
              opacity: particleOpacity,
            }}
          />
        );
      })}
    </div>
  );
};

/** Text with glow animation */
const GlowingTextInline: React.FC<{
  text: string;
  fontSize: number;
  color: string;
  glowColor: string;
  enterStart: number;
  enterEnd: number;
  fontWeight?: number;
  letterSpacing?: number;
  textTransform?: React.CSSProperties["textTransform"];
  frame: number;
}> = ({
  text,
  fontSize,
  color,
  glowColor,
  enterStart,
  enterEnd,
  fontWeight = 700,
  letterSpacing = 0,
  textTransform = "none",
  frame,
}) => {
  const opacity = interpolate(frame, [enterStart, enterEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(3)),
  });

  const translateY = interpolate(frame, [enterStart, enterEnd], [24, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(3)),
  });

  const glowIntensity =
    frame > enterEnd
      ? interpolate(
          Math.sin(((frame - enterEnd) / 60) * Math.PI * 2),
          [-1, 1],
          [0.5, 1],
        )
      : interpolate(frame, [enterStart, enterEnd], [0, 0.7], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        });

  return (
    <div
      style={{
        opacity,
        transform: `translateY(${translateY}px)`,
        fontSize,
        fontWeight,
        fontFamily: "'Inter', 'Helvetica Neue', Arial, sans-serif",
        color,
        letterSpacing,
        textTransform,
        textShadow: `0 0 ${30 * glowIntensity}px ${glowColor}, 0 0 ${60 * glowIntensity}px ${glowColor}`,
        whiteSpace: "nowrap",
        textAlign: "center" as const,
        lineHeight: 1.1,
      }}
    >
      {text}
    </div>
  );
};

// ── Main Component ────────────────────────────────────────────

export const ColdOpen08PddTitleCard: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  // ── Background video overlay ────────────────────────────────
  const bgVideoSrc = staticFile("veo/developer_prompt_shift.mp4");
  const bgVideoOpacity = interpolate(frame, [0, 20], [0.08, 0.15], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Center divider animation ────────────────────────────────
  const dividerWidth = interpolate(
    frame,
    [DIVIDER_DRAW_START, DIVIDER_DRAW_END],
    [0, 480],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(4)),
    },
  );

  const dividerOpacity = interpolate(
    frame,
    [DIVIDER_DRAW_START, DIVIDER_DRAW_START + 6],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    },
  );

  // ── Corner bracket decorations ──────────────────────────────
  const bracketOpacity = interpolate(frame, [8, 22], [0, 0.8], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(3)),
  });

  const bracketSize = 40;
  const bracketInset = 60;
  const bracketStroke = 2;

  // ── Radial glow behind title ────────────────────────────────
  const glowScale = interpolate(frame, [0, 25], [0.6, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(3)),
  });

  const glowPulse =
    frame > 25
      ? interpolate(
          Math.sin(((frame - 25) / 60) * Math.PI * 2),
          [-1, 1],
          [0.85, 1.05],
        )
      : 1;

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${BG_GRADIENT_TOP} 0%, ${BG_COLOR} 50%, ${BG_GRADIENT_BOTTOM} 100%)`,
      }}
    >
      {/* Background video layer */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          opacity: bgVideoOpacity,
        }}
      >
        <OffthreadVideo
          src={bgVideoSrc}
          style={{
            width: "100%",
            height: "100%",
            objectFit: "cover",
          }}
          muted
        />
      </div>

      {/* Animated grid + particles */}
      <AnimatedGridInline width={width} height={height} frame={frame} />

      {/* Radial glow behind title area */}
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: "50%",
          width: 800,
          height: 400,
          transform: `translate(-50%, -55%) scale(${glowScale * glowPulse})`,
          background: `radial-gradient(ellipse at center, ${GLOW_BLUE} 0%, ${GLOW_CYAN} 40%, transparent 70%)`,
          borderRadius: "50%",
          pointerEvents: "none",
        }}
      />

      {/* Corner brackets (top-left) */}
      <svg
        width={bracketSize}
        height={bracketSize}
        style={{
          position: "absolute",
          top: bracketInset,
          left: bracketInset,
          opacity: bracketOpacity,
        }}
      >
        <polyline
          points={`0,${bracketSize} 0,0 ${bracketSize},0`}
          fill="none"
          stroke={ACCENT_BLUE}
          strokeWidth={bracketStroke}
        />
      </svg>

      {/* Corner brackets (top-right) */}
      <svg
        width={bracketSize}
        height={bracketSize}
        style={{
          position: "absolute",
          top: bracketInset,
          right: bracketInset,
          opacity: bracketOpacity,
        }}
      >
        <polyline
          points={`0,0 ${bracketSize},0 ${bracketSize},${bracketSize}`}
          fill="none"
          stroke={ACCENT_BLUE}
          strokeWidth={bracketStroke}
        />
      </svg>

      {/* Corner brackets (bottom-left) */}
      <svg
        width={bracketSize}
        height={bracketSize}
        style={{
          position: "absolute",
          bottom: bracketInset,
          left: bracketInset,
          opacity: bracketOpacity,
        }}
      >
        <polyline
          points={`0,0 0,${bracketSize} ${bracketSize},${bracketSize}`}
          fill="none"
          stroke={ACCENT_BLUE}
          strokeWidth={bracketStroke}
        />
      </svg>

      {/* Corner brackets (bottom-right) */}
      <svg
        width={bracketSize}
        height={bracketSize}
        style={{
          position: "absolute",
          bottom: bracketInset,
          right: bracketInset,
          opacity: bracketOpacity,
        }}
      >
        <polyline
          points={`${bracketSize},0 ${bracketSize},${bracketSize} 0,${bracketSize}`}
          fill="none"
          stroke={ACCENT_BLUE}
          strokeWidth={bracketStroke}
        />
      </svg>

      {/* ── Center Content ──────────────────────────────────── */}
      <AbsoluteFill
        style={{
          display: "flex",
          flexDirection: "column",
          justifyContent: "center",
          alignItems: "center",
        }}
      >
        {/* Section label */}
        <GlowingTextInline
          text="COLD OPEN"
          fontSize={LABEL_FONT_SIZE}
          color={ACCENT_CYAN}
          glowColor={GLOW_CYAN}
          enterStart={TITLE_ENTER_START}
          enterEnd={TITLE_ENTER_START + 12}
          fontWeight={600}
          letterSpacing={6}
          textTransform="uppercase"
          frame={frame}
        />

        <div style={{ height: 20 }} />

        {/* Main Title — PDD */}
        <GlowingTextInline
          text="Prompt-Driven"
          fontSize={TITLE_FONT_SIZE}
          color={TEXT_WHITE}
          glowColor={GLOW_BLUE}
          enterStart={TITLE_ENTER_START}
          enterEnd={TITLE_ENTER_END}
          fontWeight={800}
          letterSpacing={-2}
          frame={frame}
        />

        <GlowingTextInline
          text="Development"
          fontSize={TITLE_FONT_SIZE}
          color={ACCENT_BLUE}
          glowColor={GLOW_BLUE}
          enterStart={TITLE_ENTER_START + 4}
          enterEnd={TITLE_ENTER_END + 4}
          fontWeight={800}
          letterSpacing={-2}
          frame={frame}
        />

        <div style={{ height: 24 }} />

        {/* Animated horizontal divider */}
        <div
          style={{
            width: dividerWidth,
            height: DIVIDER_THICKNESS,
            backgroundColor: DIVIDER_COLOR,
            opacity: dividerOpacity,
            borderRadius: DIVIDER_THICKNESS / 2,
            boxShadow: `0 0 12px ${GLOW_BLUE}, 0 0 24px ${GLOW_BLUE}`,
          }}
        />

        <div style={{ height: 24 }} />

        {/* Subtitle */}
        <GlowingTextInline
          text="When AI Writes the First Draft"
          fontSize={SUBTITLE_FONT_SIZE}
          color={TEXT_DIM}
          glowColor="rgba(148, 163, 184, 0.15)"
          enterStart={SUBTITLE_ENTER_START}
          enterEnd={SUBTITLE_ENTER_END}
          fontWeight={400}
          letterSpacing={1}
          frame={frame}
        />
      </AbsoluteFill>

      {/* ── Bottom label ────────────────────────────────────── */}
      <div
        style={{
          position: "absolute",
          bottom: 48,
          left: 0,
          width: "100%",
          display: "flex",
          justifyContent: "center",
          opacity: interpolate(frame, [24, 38], [0, 0.78], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }),
        }}
      >
        <div
          style={{
            fontSize: 18,
            fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
            color: TEXT_DIM,
            letterSpacing: 3,
            textTransform: "uppercase" as const,
          }}
        >
          // section_08
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen08PddTitleCard;
