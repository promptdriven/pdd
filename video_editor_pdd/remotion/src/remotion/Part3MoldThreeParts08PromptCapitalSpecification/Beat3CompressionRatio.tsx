import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  spring,
  useVideoConfig,
} from 'remotion';
import {
  NOZZLE_BLUE,
  MUTED_GRAY,
  CODE_DIM,
  PANEL_BG,
  PANEL_BORDER,
  TEXT_LIGHT,
  PROMPT_LINES,
  DENSE_CODE_LINES,
} from './constants';

// ── Prompt panel (left) ──
const PromptPanel: React.FC<{ opacity: number }> = ({ opacity }) => (
  <div
    style={{
      position: 'absolute',
      left: 100,
      top: 180,
      width: 300,
      height: 300,
      backgroundColor: PANEL_BG,
      border: `1px solid ${PANEL_BORDER}`,
      borderRadius: 6,
      padding: '12px 14px',
      opacity,
      boxShadow: `0 0 30px ${NOZZLE_BLUE}1A`,
    }}
  >
    <div
      style={{
        fontFamily: 'JetBrains Mono, monospace',
        fontSize: 10,
        lineHeight: '18px',
        color: NOZZLE_BLUE,
        opacity: 0.7,
        whiteSpace: 'pre-wrap',
      }}
    >
      {PROMPT_LINES.map((line, i) => (
        <div key={i}>{line || '\u00A0'}</div>
      ))}
    </div>
  </div>
);

// ── Scrolling code panel (right of prompt) ──
const CodeScrollPanel: React.FC<{ scrollOffset: number; opacity: number }> = ({
  scrollOffset,
  opacity,
}) => (
  <div
    style={{
      position: 'absolute',
      left: 450,
      top: 80,
      width: 300,
      height: 600,
      backgroundColor: PANEL_BG,
      border: `1px solid ${PANEL_BORDER}`,
      borderRadius: 6,
      overflow: 'hidden',
      opacity,
    }}
  >
    <div
      style={{
        position: 'absolute',
        top: -scrollOffset,
        left: 10,
        right: 10,
        fontFamily: 'JetBrains Mono, monospace',
        fontSize: 8,
        lineHeight: '12px',
        color: CODE_DIM,
        opacity: 0.3,
        whiteSpace: 'pre',
      }}
    >
      {DENSE_CODE_LINES.map((line, i) => (
        <div key={i}>{line}</div>
      ))}
    </div>
  </div>
);

// ── Height comparison arrow ──
const HeightArrow: React.FC<{ opacity: number }> = ({ opacity }) => (
  <svg
    width={40}
    height={500}
    style={{
      position: 'absolute',
      left: 415,
      top: 130,
      opacity,
    }}
  >
    {/* Arrow line */}
    <line
      x1={20}
      y1={50}
      x2={20}
      y2={450}
      stroke={NOZZLE_BLUE}
      strokeWidth={1.5}
      opacity={0.5}
    />
    {/* Top arrow head */}
    <path d="M 14 60 L 20 50 L 26 60" stroke={NOZZLE_BLUE} fill="none" strokeWidth={1.5} opacity={0.5} />
    {/* Bottom arrow head */}
    <path d="M 14 440 L 20 450 L 26 440" stroke={NOZZLE_BLUE} fill="none" strokeWidth={1.5} opacity={0.5} />
    {/* Label */}
    <text
      x={20}
      y={255}
      textAnchor="middle"
      fontFamily="Inter, sans-serif"
      fontSize={14}
      fontWeight={700}
      fill={NOZZLE_BLUE}
      opacity={0.7}
    >
      10×
    </text>
  </svg>
);

// ── Ratio badge ──
const RatioBadge: React.FC<{ scale: number }> = ({ scale }) => (
  <div
    style={{
      position: 'absolute',
      left: 250,
      top: 530,
      transform: `translateX(-50%) scale(${scale})`,
      backgroundColor: `${NOZZLE_BLUE}1A`,
      border: `1px solid ${NOZZLE_BLUE}33`,
      borderRadius: 20,
      padding: '6px 18px',
      fontFamily: 'Inter, sans-serif',
      fontSize: 24,
      fontWeight: 700,
      color: NOZZLE_BLUE,
      whiteSpace: 'nowrap',
    }}
  >
    1:5 to 1:10
  </div>
);

// ── Context window (single) ──
const ContextWindow: React.FC<{
  x: number;
  y: number;
  width: number;
  height: number;
  label: string;
  labelColor: string;
  fillColor: string;
  fillOpacity: number;
  style: 'dense' | 'clean_blocks';
  opacity: number;
  pulse?: number;
}> = ({ x, y, width, height, label, labelColor, fillColor, fillOpacity, style, opacity, pulse = 0 }) => {
  const blockCount = style === 'dense' ? 60 : 10;
  const blockHeight = style === 'dense' ? 8 : 40;
  const gap = style === 'dense' ? 2 : 12;

  return (
    <div style={{ position: 'absolute', left: x, top: y, opacity }}>
      {/* Label above */}
      <div
        style={{
          position: 'absolute',
          top: -22,
          left: 0,
          width,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 11,
          color: labelColor,
        }}
      >
        {label}
      </div>

      {/* Window */}
      <div
        style={{
          width,
          height,
          backgroundColor: PANEL_BG,
          border: `1px solid ${PANEL_BORDER}`,
          borderRadius: 6,
          overflow: 'hidden',
          padding: style === 'dense' ? '6px 8px' : '12px 16px',
          boxShadow: pulse > 0 ? `0 0 ${20 * pulse}px ${fillColor}33` : 'none',
        }}
      >
        {Array.from({ length: blockCount }).map((_, i) => {
          const lineWidth =
            style === 'dense'
              ? `${60 + Math.sin(i * 1.7) * 30}%`
              : `${70 + Math.sin(i * 2.3) * 20}%`;

          return (
            <div
              key={i}
              style={{
                height: blockHeight,
                width: lineWidth,
                backgroundColor: fillColor,
                opacity: fillOpacity,
                borderRadius: style === 'dense' ? 1 : 4,
                marginBottom: gap,
              }}
            />
          );
        })}
      </div>
    </div>
  );
};

export const Beat3CompressionRatio: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Panel fade-in (frames 0-30 of this beat)
  const panelFade = interpolate(frame, [0, 30], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Code scroll (continuous from frame 30)
  const scrollOffset = Math.max(0, (frame - 30) * 0.5);

  // Height arrow (frame 30-60)
  const arrowOpacity = interpolate(frame, [30, 60], [0, 1], {
    extrapolateRight: 'clamp',
  });

  // Ratio badge spring (frame 30)
  const badgeFrame = frame - 30;
  const badgeScale =
    badgeFrame >= 0
      ? spring({
          frame: badgeFrame,
          fps,
          config: { stiffness: 150, damping: 12 },
          from: 0.8,
          to: 1,
        })
      : 0;

  // Context windows slide in (frame 90)
  const ctxFrame = frame - 90;
  const ctxProgress =
    ctxFrame >= 0
      ? interpolate(ctxFrame, [0, 25], [0, 1], {
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.cubic),
        })
      : 0;
  const ctxSlideX = interpolate(ctxProgress, [0, 1], [40, 0]);
  const ctxOpacity = ctxProgress;

  // Caption (frame 150, absolute 510)
  const captionOpacity = interpolate(frame, [150, 170], [0, 1], {
    extrapolateRight: 'clamp',
  });

  // Blue pulse on right window (frames 180-240, 40-frame cycle)
  const pulseActive = frame >= 180;
  const pulseCycle = pulseActive
    ? interpolate(
        Math.sin(((frame - 180) / 40) * Math.PI * 2),
        [-1, 1],
        [0, 0.4]
      )
    : 0;

  return (
    <AbsoluteFill>
      {/* Prompt panel */}
      <PromptPanel opacity={panelFade} />

      {/* Scrolling code panel */}
      <CodeScrollPanel scrollOffset={scrollOffset} opacity={panelFade} />

      {/* Height arrow */}
      <HeightArrow opacity={arrowOpacity * panelFade} />

      {/* Ratio badge */}
      {badgeFrame >= 0 && <RatioBadge scale={badgeScale} />}

      {/* Context window comparison */}
      <div
        style={{
          position: 'absolute',
          left: ctxSlideX,
          top: 0,
          opacity: ctxOpacity,
        }}
      >
        {/* LEFT: dense code */}
        <ContextWindow
          x={900}
          y={200}
          width={380}
          height={500}
          label="15,000 tokens of code"
          labelColor={MUTED_GRAY}
          fillColor={CODE_DIM}
          fillOpacity={0.15}
          style="dense"
          opacity={1}
        />

        {/* RIGHT: clean prompts */}
        <ContextWindow
          x={1320}
          y={200}
          width={380}
          height={500}
          label="Prompts for 10 modules"
          labelColor={NOZZLE_BLUE}
          fillColor={NOZZLE_BLUE}
          fillOpacity={0.15}
          style="clean_blocks"
          opacity={1}
          pulse={pulseCycle}
        />
      </div>

      {/* Caption below context windows */}
      <div
        style={{
          position: 'absolute',
          left: 900,
          top: 730,
          width: 800,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          color: TEXT_LIGHT,
          opacity: captionOpacity * 0.7,
          lineHeight: '22px',
        }}
      >
        Same context window. <strong>10× more system knowledge.</strong>
      </div>
    </AbsoluteFill>
  );
};
