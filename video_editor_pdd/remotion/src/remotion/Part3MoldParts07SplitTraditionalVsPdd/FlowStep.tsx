import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  STEP_HEIGHT,
  STEP_BORDER_RADIUS,
  STEP_FILL,
  STEP_TEXT_COLOR,
  STEP_TEXT_SIZE,
  STEP_FONT_WEIGHT,
  CODE_FONT_SIZE,
  PDD_CODE_COLOR,
  PDD_FINAL_BORDER_COLOR,
  PDD_CHECKMARK_COLOR,
  GLOW_BLUR,
  GLOW_CYCLE_FRAMES,
  FADE_IN_DURATION,
  TRAD_BANDAID_COLOR,
} from './constants';

interface FlowStepProps {
  text: string;
  width: number;
  borderColor: string;
  appearFrame: number;
  hasBandaid: boolean;
  hasCode: boolean;
  codeText?: string;
  isFinal: boolean;
}

const BandAidIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width={16} height={16} viewBox="0 0 16 16" style={{ marginLeft: 6, flexShrink: 0 }}>
    {/* Horizontal band */}
    <rect x={1} y={5} width={14} height={6} rx={3} fill={color} />
    {/* Vertical band */}
    <rect x={5} y={1} width={6} height={14} rx={3} fill={color} opacity={0.6} />
    {/* Center dots */}
    <circle cx={6.5} cy={7} r={0.8} fill="#0A0F1A" />
    <circle cx={9.5} cy={7} r={0.8} fill="#0A0F1A" />
    <circle cx={6.5} cy={9.5} r={0.8} fill="#0A0F1A" />
    <circle cx={9.5} cy={9.5} r={0.8} fill="#0A0F1A" />
  </svg>
);

export const FlowStep: React.FC<FlowStepProps> = ({
  text,
  width,
  borderColor,
  appearFrame,
  hasBandaid,
  hasCode,
  codeText,
  isFinal,
}) => {
  const frame = useCurrentFrame();

  // Fade-in opacity
  const opacity = interpolate(
    frame,
    [appearFrame, appearFrame + FADE_IN_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Scale for entrance
  const scale = interpolate(
    frame,
    [appearFrame, appearFrame + FADE_IN_DURATION],
    [0.9, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Final step glow pulse
  let glowIntensity = 0;
  if (isFinal && frame >= appearFrame + FADE_IN_DURATION) {
    const cycleFrame = (frame - appearFrame - FADE_IN_DURATION) % GLOW_CYCLE_FRAMES;
    glowIntensity = interpolate(
      cycleFrame,
      [0, GLOW_CYCLE_FRAMES / 2, GLOW_CYCLE_FRAMES],
      [0.12, 0.25, 0.12],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
    );
  }

  const activeBorder = isFinal ? PDD_FINAL_BORDER_COLOR : borderColor;
  const glowShadow = isFinal
    ? `0 0 ${GLOW_BLUR}px rgba(74, 222, 128, ${glowIntensity})`
    : 'none';

  // Parse text for code segments
  const renderText = () => {
    if (hasCode && codeText) {
      // Split at code portion — text is like "Add test " with code "pdd bug"
      return (
        <span style={{ display: 'flex', alignItems: 'center', gap: 0 }}>
          <span>{text}</span>
          <span style={{ fontFamily: 'JetBrains Mono, monospace', fontSize: CODE_FONT_SIZE, color: PDD_CODE_COLOR }}>
            ({codeText})
          </span>
        </span>
      );
    }
    return <span>{text}</span>;
  };

  return (
    <div
      style={{
        opacity,
        transform: `scale(${scale})`,
        width,
        height: STEP_HEIGHT,
        borderRadius: STEP_BORDER_RADIUS,
        backgroundColor: STEP_FILL,
        border: `1px solid ${activeBorder}`,
        boxShadow: glowShadow,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        padding: '0 12px',
        boxSizing: 'border-box',
      }}
    >
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: STEP_TEXT_SIZE,
          fontWeight: STEP_FONT_WEIGHT,
          color: isFinal ? PDD_CHECKMARK_COLOR : STEP_TEXT_COLOR,
          display: 'flex',
          alignItems: 'center',
          whiteSpace: 'nowrap',
        }}
      >
        {renderText()}
        {hasBandaid && <BandAidIcon color={TRAD_BANDAID_COLOR} />}
      </span>
    </div>
  );
};

export default FlowStep;
