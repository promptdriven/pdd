import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CHIP_OUTLINE,
  CHIP_FILL_OPACITY,
  CHIP_LABEL_COLOR,
  CHIP_X,
  CHIP_Y,
  CHIP_WIDTH,
  CHIP_HEIGHT,
  CHIP_FADE_START,
  CHIP_FADE_END,
  GATE_STREAM_START,
  SYNTAX_KEYWORD,
} from './constants';

/**
 * Renders the synthesis processor chip with input/output arrows.
 * Fades in from CHIP_FADE_START. Input arrow pulses once gate stream begins.
 */
export const SynthesisChip: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < CHIP_FADE_START) return null;

  // Fade in
  const fadeIn = interpolate(
    frame,
    [CHIP_FADE_START, CHIP_FADE_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Arrow pulse (easeInOut sine, 30-frame cycle)
  const pulsePhase = frame >= GATE_STREAM_START
    ? interpolate(
        (frame - GATE_STREAM_START) % 30,
        [0, 15, 30],
        [0, 1, 0],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
      )
    : 0;

  const arrowGlow = 0.5 + pulsePhase * 0.5;

  // Code symbols flowing into the chip (left side)
  const codeSymbols = ['m', 'o', 'd', 'u', 'l', 'e', ' ', '@', '+', '='];
  const symbolsVisible = frame >= GATE_STREAM_START;

  // Chip pin decorations
  const pinCount = 6;
  const pinSpacing = CHIP_HEIGHT / (pinCount + 1);

  return (
    <div
      style={{
        position: 'absolute',
        left: CHIP_X - CHIP_WIDTH / 2 - 200,
        top: CHIP_Y - CHIP_HEIGHT / 2 - 40,
        width: CHIP_WIDTH + 400,
        height: CHIP_HEIGHT + 80,
        opacity: fadeIn,
      }}
    >
      <svg
        width={CHIP_WIDTH + 400}
        height={CHIP_HEIGHT + 80}
        viewBox={`0 0 ${CHIP_WIDTH + 400} ${CHIP_HEIGHT + 80}`}
      >
        {/* Input arrow (left) */}
        <line
          x1={30}
          y1={(CHIP_HEIGHT + 80) / 2}
          x2={195}
          y2={(CHIP_HEIGHT + 80) / 2}
          stroke={CHIP_OUTLINE}
          strokeWidth={2}
          opacity={arrowGlow}
        />
        <polygon
          points={`195,${(CHIP_HEIGHT + 80) / 2 - 6} 205,${(CHIP_HEIGHT + 80) / 2} 195,${(CHIP_HEIGHT + 80) / 2 + 6}`}
          fill={CHIP_OUTLINE}
          opacity={arrowGlow}
        />

        {/* Flowing code symbols into chip */}
        {symbolsVisible &&
          codeSymbols.map((sym, i) => {
            const progress = ((frame - GATE_STREAM_START + i * 8) % 80) / 80;
            const sx = 40 + progress * 150;
            const symOpacity = progress < 0.1 ? progress / 0.1 : progress > 0.85 ? (1 - progress) / 0.15 : 0.8;
            return (
              <text
                key={`sym-${i}`}
                x={sx}
                y={(CHIP_HEIGHT + 80) / 2 - 12}
                fill={SYNTAX_KEYWORD}
                fontSize={12}
                fontFamily='"JetBrains Mono", monospace'
                opacity={symOpacity}
              >
                {sym}
              </text>
            );
          })}

        {/* Chip body */}
        <rect
          x={200}
          y={40}
          width={CHIP_WIDTH}
          height={CHIP_HEIGHT}
          rx={6}
          ry={6}
          fill={CHIP_OUTLINE}
          fillOpacity={CHIP_FILL_OPACITY}
          stroke={CHIP_OUTLINE}
          strokeWidth={2}
        />

        {/* Chip pins (left) */}
        {Array.from({ length: pinCount }).map((_, i) => (
          <rect
            key={`pin-l-${i}`}
            x={192}
            y={40 + pinSpacing * (i + 1) - 3}
            width={10}
            height={6}
            fill={CHIP_OUTLINE}
            opacity={0.6}
            rx={1}
          />
        ))}

        {/* Chip pins (right) */}
        {Array.from({ length: pinCount }).map((_, i) => (
          <rect
            key={`pin-r-${i}`}
            x={200 + CHIP_WIDTH - 2}
            y={40 + pinSpacing * (i + 1) - 3}
            width={10}
            height={6}
            fill={CHIP_OUTLINE}
            opacity={0.6}
            rx={1}
          />
        ))}

        {/* Label: SYNTHESIS */}
        <text
          x={200 + CHIP_WIDTH / 2}
          y={40 + CHIP_HEIGHT / 2 + 5}
          textAnchor="middle"
          fill={CHIP_LABEL_COLOR}
          fontSize={14}
          fontFamily='Inter, system-ui, sans-serif'
          fontWeight={600}
          letterSpacing={2}
        >
          SYNTHESIS
        </text>

        {/* Output arrow (right) */}
        <line
          x1={200 + CHIP_WIDTH + 8}
          y1={(CHIP_HEIGHT + 80) / 2}
          x2={CHIP_WIDTH + 370}
          y2={(CHIP_HEIGHT + 80) / 2}
          stroke={CHIP_OUTLINE}
          strokeWidth={2}
          opacity={arrowGlow}
        />
        <polygon
          points={`${CHIP_WIDTH + 370},${(CHIP_HEIGHT + 80) / 2 - 6} ${CHIP_WIDTH + 380},${(CHIP_HEIGHT + 80) / 2} ${CHIP_WIDTH + 370},${(CHIP_HEIGHT + 80) / 2 + 6}`}
          fill={CHIP_OUTLINE}
          opacity={arrowGlow}
        />
      </svg>
    </div>
  );
};
