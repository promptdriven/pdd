import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
  spring,
} from "remotion";
import {
  BG_COLOR,
  LAYER_BG_INNER,
  LAYER_BG_MID,
  LAYER_BG_OUTER,
  TEXT_PRIMARY,
  TEXT_SECONDARY,
  ACCENT_BLUE,
  ACCENT_GREEN,
  ACCENT_AMBER,
  ACCENT_PURPLE,
  DIVIDER_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  LAYER_CARD_WIDTH,
  LAYER_CARD_HEIGHT,
  LAYER_GAP,
  PHASE_INNER_END,
  PHASE_MID_ZOOM_START,
  PHASE_MID_ZOOM_END,
  PHASE_OUTER_ZOOM_START,
  PHASE_OUTER_ZOOM_END,
  PHASE_FULL_ZOOM_START,
  PHASE_FULL_ZOOM_END,
  PHASE_HOLD_START,
  TOTAL_DURATION_FRAMES,
  LAYER_LABELS,
} from "./constants";
import { LayerCard } from "./LayerCard";
import { ConnectorLinesGroup } from "./ConnectorLines";

// ── Default props (empty, self-contained) ──
export const defaultColdOpen04ZoomOutAccumulatedProps = {};

// ── Grid background pattern ──
const GridBackground: React.FC<{ opacity: number }> = ({ opacity }) => (
  <div
    style={{
      position: "absolute",
      inset: 0,
      opacity,
      backgroundImage: `
        linear-gradient(rgba(59,130,246,0.06) 1px, transparent 1px),
        linear-gradient(90deg, rgba(59,130,246,0.06) 1px, transparent 1px)
      `,
      backgroundSize: "60px 60px",
    }}
  />
);

// ── Floating particle dots ──
const FloatingParticles: React.FC<{ frame: number }> = ({ frame }) => {
  const particles = React.useMemo(() => {
    const result: Array<{
      x: number;
      y: number;
      size: number;
      speed: number;
      color: string;
      phaseOffset: number;
    }> = [];
    const colors = [ACCENT_BLUE, ACCENT_GREEN, ACCENT_AMBER, ACCENT_PURPLE];
    for (let i = 0; i < 24; i++) {
      // Deterministic pseudo-random using index
      const seed = (i * 7919 + 1) % 997;
      result.push({
        x: (seed % 1920),
        y: ((seed * 3) % 1080),
        size: 2 + (seed % 4),
        speed: 0.3 + (seed % 10) / 20,
        color: colors[i % colors.length],
        phaseOffset: (seed % 60),
      });
    }
    return result;
  }, []);

  return (
    <>
      {particles.map((p, i) => {
        const yOffset = Math.sin((frame + p.phaseOffset) * 0.04 * p.speed) * 30;
        const xOffset = Math.cos((frame + p.phaseOffset) * 0.03 * p.speed) * 20;
        const particleOpacity = interpolate(
          Math.sin((frame + p.phaseOffset) * 0.05),
          [-1, 1],
          [0.1, 0.4]
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
              backgroundColor: p.color,
              opacity: particleOpacity,
              boxShadow: `0 0 ${p.size * 2}px ${p.color}40`,
            }}
          />
        );
      })}
    </>
  );
};

// ── Title overlay that appears at final zoom ──
const TitleOverlay: React.FC<{ frame: number; fps: number }> = ({
  frame,
  fps,
}) => {
  const titleOpacity = interpolate(
    frame,
    [PHASE_FULL_ZOOM_START + 10, PHASE_FULL_ZOOM_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const titleY = interpolate(
    frame,
    [PHASE_FULL_ZOOM_START + 10, PHASE_FULL_ZOOM_END],
    [30, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  // Subtle scale pulse in hold phase
  const holdPulse = interpolate(
    frame,
    [PHASE_HOLD_START, PHASE_HOLD_START + 15, PHASE_HOLD_START + 30],
    [1, 1.02, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <div
      style={{
        position: "absolute",
        top: 48,
        left: 0,
        right: 0,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        opacity: titleOpacity,
        transform: `translateY(${titleY}px) scale(${holdPulse})`,
      }}
    >
      <div
        style={{
          fontSize: 18,
          fontFamily: "monospace",
          color: ACCENT_BLUE,
          letterSpacing: "0.2em",
          textTransform: "uppercase",
          fontWeight: 600,
          marginBottom: 12,
          opacity: 0.9,
        }}
      >
        Accumulated View
      </div>
      <div
        style={{
          fontSize: 48,
          fontWeight: 800,
          color: TEXT_PRIMARY,
          fontFamily: "Inter, system-ui, sans-serif",
          letterSpacing: "-0.03em",
          textAlign: "center",
        }}
      >
        Every Layer Matters
      </div>
      {/* Divider rule */}
      <div
        style={{
          width: 120,
          height: 3,
          backgroundColor: DIVIDER_COLOR,
          marginTop: 16,
          borderRadius: 2,
          opacity: 0.85,
        }}
      />
    </div>
  );
};

// ── Ring decoration around zoomed-out layers ──
const LayerRing: React.FC<{
  frame: number;
  revealFrame: number;
  radius: number;
  color: string;
}> = ({ frame, revealFrame, radius, color }) => {
  const ringOpacity = interpolate(
    frame,
    [revealFrame, revealFrame + 25],
    [0, 0.25],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const ringScale = interpolate(
    frame,
    [revealFrame, revealFrame + 30],
    [0.8, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: "50%",
        top: "50%",
        width: radius * 2,
        height: radius * 2,
        marginLeft: -radius,
        marginTop: -radius + 60,
        borderRadius: "50%",
        border: `2px solid ${color}`,
        opacity: ringOpacity,
        transform: `scale(${ringScale})`,
        boxShadow: `0 0 20px ${color}20`,
      }}
    />
  );
};

// ── Main component ──
export const ColdOpen04ZoomOutAccumulated: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // ── Zoom scale: starts zoomed in (3x), progressively zooms out to 1x ──
  const zoomScale = interpolate(
    frame,
    [0, PHASE_INNER_END, PHASE_MID_ZOOM_END, PHASE_OUTER_ZOOM_END, PHASE_FULL_ZOOM_END],
    [3, 3, 2, 1.4, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  // ── Pan Y: camera moves up as we zoom out to reveal stacked layers ──
  const panY = interpolate(
    frame,
    [0, PHASE_INNER_END, PHASE_MID_ZOOM_END, PHASE_OUTER_ZOOM_END, PHASE_FULL_ZOOM_END],
    [-200, -200, -50, 50, 80],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.poly(3)),
    }
  );

  // ── Grid fade ──
  const gridOpacity = interpolate(frame, [0, 30], [0.3, 0.6], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Vignette ──
  const vignetteOpacity = interpolate(frame, [0, PHASE_FULL_ZOOM_END], [0.4, 0.2], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Layer vertical positions (stacked, centered horizontally) ──
  const cardTotalHeight = LAYER_CARD_HEIGHT + LAYER_GAP;
  const stackBaseY = CANVAS_HEIGHT / 2 - LAYER_CARD_HEIGHT / 2;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Background grid */}
      <GridBackground opacity={gridOpacity} />

      {/* Floating particles */}
      <FloatingParticles frame={frame} />

      {/* Main zoom container */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          transform: `scale(${zoomScale}) translateY(${panY}px)`,
          transformOrigin: "center center",
          willChange: "transform",
        }}
      >
        {/* Decorative rings around layer groups */}
        <LayerRing
          frame={frame}
          revealFrame={PHASE_MID_ZOOM_START}
          radius={360}
          color={ACCENT_BLUE}
        />
        <LayerRing
          frame={frame}
          revealFrame={PHASE_OUTER_ZOOM_START}
          radius={560}
          color={ACCENT_GREEN}
        />

        {/* Connector lines between layers */}
        <ConnectorLinesGroup zoomScale={zoomScale} panY={panY} />

        {/* Layer 1: Inner – "The Code" (visible from frame 0) */}
        <div
          style={{
            position: "absolute",
            left: CANVAS_WIDTH / 2 - LAYER_CARD_WIDTH / 2,
            top: stackBaseY - cardTotalHeight,
            display: "flex",
            justifyContent: "center",
          }}
        >
          <LayerCard
            title={LAYER_LABELS[0].title}
            subtitle={LAYER_LABELS[0].subtitle}
            icon={LAYER_LABELS[0].icon}
            bgColor={LAYER_BG_INNER}
            accentColor={ACCENT_BLUE}
            revealFrame={0}
            cardIndex={0}
          />
        </div>

        {/* Layer 2: Mid – "The Context" (revealed during zoom phase 2) */}
        <div
          style={{
            position: "absolute",
            left: CANVAS_WIDTH / 2 - LAYER_CARD_WIDTH / 2,
            top: stackBaseY,
            display: "flex",
            justifyContent: "center",
          }}
        >
          <LayerCard
            title={LAYER_LABELS[1].title}
            subtitle={LAYER_LABELS[1].subtitle}
            icon={LAYER_LABELS[1].icon}
            bgColor={LAYER_BG_MID}
            accentColor={ACCENT_GREEN}
            revealFrame={PHASE_MID_ZOOM_START}
            cardIndex={1}
          />
        </div>

        {/* Layer 3: Outer – "The System" (revealed during zoom phase 3) */}
        <div
          style={{
            position: "absolute",
            left: CANVAS_WIDTH / 2 - LAYER_CARD_WIDTH / 2,
            top: stackBaseY + cardTotalHeight,
            display: "flex",
            justifyContent: "center",
          }}
        >
          <LayerCard
            title={LAYER_LABELS[2].title}
            subtitle={LAYER_LABELS[2].subtitle}
            icon={LAYER_LABELS[2].icon}
            bgColor={LAYER_BG_OUTER}
            accentColor={ACCENT_PURPLE}
            revealFrame={PHASE_OUTER_ZOOM_START}
            cardIndex={2}
          />
        </div>

        {/* Layer index labels on the side */}
        {[0, 1, 2].map((i) => {
          const layerRevealFrames = [0, PHASE_MID_ZOOM_START, PHASE_OUTER_ZOOM_START];
          const labelOpacity = interpolate(
            frame,
            [layerRevealFrames[i] + 5, layerRevealFrames[i] + 25],
            [0, 0.7],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );
          const labelColors = [ACCENT_BLUE, ACCENT_GREEN, ACCENT_PURPLE];
          return (
            <div
              key={`label-${i}`}
              style={{
                position: "absolute",
                left: CANVAS_WIDTH / 2 - LAYER_CARD_WIDTH / 2 - 80,
                top: stackBaseY - cardTotalHeight + i * cardTotalHeight + LAYER_CARD_HEIGHT / 2 - 12,
                opacity: labelOpacity,
                fontSize: 22,
                fontFamily: "monospace",
                color: labelColors[i],
                fontWeight: 700,
                textAlign: "right",
                width: 60,
              }}
            >
              L{i + 1}
            </div>
          );
        })}
      </div>

      {/* Title overlay (appears at final zoom) */}
      <TitleOverlay frame={frame} fps={fps} />

      {/* Bottom status bar */}
      <div
        style={{
          position: "absolute",
          bottom: 32,
          left: 0,
          right: 0,
          display: "flex",
          justifyContent: "center",
          alignItems: "center",
          gap: 24,
          opacity: interpolate(
            frame,
            [PHASE_FULL_ZOOM_START, PHASE_FULL_ZOOM_END],
            [0, 0.8],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          ),
        }}
      >
        {[
          { label: "Layers", value: "3", color: ACCENT_BLUE },
          { label: "Accumulated", value: "100%", color: ACCENT_GREEN },
          { label: "Zoom", value: `${zoomScale.toFixed(1)}x`, color: ACCENT_AMBER },
        ].map((stat, i) => (
          <div
            key={stat.label}
            style={{
              display: "flex",
              alignItems: "center",
              gap: 8,
              padding: "8px 16px",
              backgroundColor: "rgba(15, 29, 50, 0.85)",
              borderRadius: 8,
              border: `1px solid ${stat.color}30`,
            }}
          >
            <div
              style={{
                width: 8,
                height: 8,
                borderRadius: "50%",
                backgroundColor: stat.color,
                boxShadow: `0 0 6px ${stat.color}60`,
              }}
            />
            <span
              style={{
                fontSize: 14,
                fontFamily: "monospace",
                color: TEXT_SECONDARY,
                fontWeight: 500,
              }}
            >
              {stat.label}
            </span>
            <span
              style={{
                fontSize: 16,
                fontFamily: "monospace",
                color: TEXT_PRIMARY,
                fontWeight: 700,
              }}
            >
              {stat.value}
            </span>
          </div>
        ))}
      </div>

      {/* Vignette overlay */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          background: `radial-gradient(ellipse at center, transparent 40%, ${BG_COLOR} 100%)`,
          opacity: vignetteOpacity,
          pointerEvents: "none",
        }}
      />
    </AbsoluteFill>
  );
};

export default ColdOpen04ZoomOutAccumulated;
