// Part3MoldParts09FiveGenerations.tsx — Main component
// Five code generation outputs shown side by side, one wins.
import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { CodePanel } from "./CodePanel";
import { StatusOverlay } from "./StatusOverlay";
import {
  BG_COLOR,
  PANEL_WIDTH,
  PANEL_HEIGHT,
  PANEL_GAP,
  PANELS_START_X,
  PANEL_Y,
  PANEL_STAGGER,
  PANEL_SLIDE_DURATION,
  PANEL_SLIDE_DISTANCE,
  STATUS_FAIL_START,
  STATUS_WARN_START,
  STATUS_PASS_START,
  HIGHLIGHT_START,
  HIGHLIGHT_SCALE_DURATION,
  DIM_DURATION,
  DIM_OPACITY,
  LABEL_START,
  LABEL_FADE_DURATION,
  LABEL_FONT,
  LABEL_SIZE,
  LABEL_COLOR,
  PASS_COLOR,
  GENERATIONS,
  GEN_CODE,
  BOTTOM_LABEL,
} from "./constants";

// ─── Default Props ────────────────────────────────────────────────────
export const defaultPart3MoldParts09FiveGenerationsProps = {};

// ─── Animated Panel Wrapper ───────────────────────────────────────────
const AnimatedPanel: React.FC<{
  index: number;
  children: React.ReactNode;
}> = ({ index, children }) => {
  const frame = useCurrentFrame();
  const panelStart = index * PANEL_STAGGER;
  const x = PANELS_START_X + index * (PANEL_WIDTH + PANEL_GAP);

  // Slide up + fade in
  const slideY = interpolate(
    frame,
    [panelStart, panelStart + PANEL_SLIDE_DURATION],
    [PANEL_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const opacity = interpolate(
    frame,
    [panelStart, panelStart + PANEL_SLIDE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Dim non-winning panels after HIGHLIGHT_START
  const dimFactor =
    index < 4
      ? interpolate(
          frame,
          [HIGHLIGHT_START, HIGHLIGHT_START + DIM_DURATION],
          [1, DIM_OPACITY],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.quad),
          }
        )
      : 1;

  // Scale up winning panel
  const scale =
    index === 4
      ? interpolate(
          frame,
          [HIGHLIGHT_START, HIGHLIGHT_START + HIGHLIGHT_SCALE_DURATION],
          [1.0, 1.08],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.quad),
          }
        )
      : 1;

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: PANEL_Y,
        width: PANEL_WIDTH,
        height: PANEL_HEIGHT,
        opacity: opacity * dimFactor,
        transform: `translateY(${slideY}px) scale(${scale})`,
        transformOrigin: "center center",
      }}
    >
      {children}
    </div>
  );
};

// ─── Pulsing Green Glow for Panel 5 ──────────────────────────────────
const GreenGlowPulse: React.FC = () => {
  const frame = useCurrentFrame();
  // Pulsing glow: oscillates between 0.2 and 0.5 opacity
  const pulsePhase = Math.sin(frame * 0.08) * 0.5 + 0.5;
  const glowOpacity = 0.2 + pulsePhase * 0.3;

  const panelX = PANELS_START_X + 4 * (PANEL_WIDTH + PANEL_GAP);

  return (
    <div
      style={{
        position: "absolute",
        left: panelX - 8,
        top: PANEL_Y - 8,
        width: PANEL_WIDTH + 16,
        height: PANEL_HEIGHT + 16,
        borderRadius: 12,
        border: `2px solid ${PASS_COLOR}`,
        boxShadow: `0 0 16px ${PASS_COLOR}80, 0 0 32px ${PASS_COLOR}40`,
        opacity: glowOpacity,
        pointerEvents: "none",
      }}
    />
  );
};

// ─── Bottom Label ─────────────────────────────────────────────────────
const BottomLabel: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [0, LABEL_FADE_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        left: 0,
        right: 0,
        top: 700,
        textAlign: "center",
        fontFamily: LABEL_FONT,
        fontSize: LABEL_SIZE,
        fontWeight: 600,
        color: LABEL_COLOR,
        opacity,
      }}
    >
      {BOTTOM_LABEL}
    </div>
  );
};

// ─── Main Component ───────────────────────────────────────────────────
export const Part3MoldParts09FiveGenerations: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine border color for panel 5 (transitions to green after checkmark)
  const panel5BorderProgress = interpolate(
    frame,
    [STATUS_PASS_START, STATUS_PASS_START + 15],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );
  const showGreenBorder = panel5BorderProgress > 0;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Five Code Panels */}
      {GENERATIONS.map((gen, i) => (
        <AnimatedPanel key={i} index={i}>
          <CodePanel
            label={`Gen ${gen.gen}`}
            code={GEN_CODE[i]}
            borderColor={
              i === 4 && showGreenBorder ? PASS_COLOR : undefined
            }
            borderGlow={i === 4 && showGreenBorder}
            glowColor={i === 4 ? PASS_COLOR : undefined}
          />

          {/* Status overlay for fail panels (1, 2) */}
          {gen.icon === "x" && (
            <Sequence from={STATUS_FAIL_START}>
              <StatusOverlay type="x" animationDuration={10} />
            </Sequence>
          )}

          {/* Status overlay for warning panels (3, 4) */}
          {gen.icon === "warning" && (
            <Sequence from={STATUS_WARN_START}>
              <StatusOverlay type="warning" animationDuration={12} />
            </Sequence>
          )}

          {/* Status overlay for pass panel (5) */}
          {gen.icon === "check" && (
            <Sequence from={STATUS_PASS_START}>
              <StatusOverlay type="check" animationDuration={15} />
            </Sequence>
          )}
        </AnimatedPanel>
      ))}

      {/* Pulsing green glow around panel 5 after highlight */}
      <Sequence from={HIGHLIGHT_START}>
        <GreenGlowPulse />
      </Sequence>

      {/* Bottom label */}
      <Sequence from={LABEL_START}>
        <BottomLabel />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3MoldParts09FiveGenerations;
