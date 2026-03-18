import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { COLORS, TIMING } from './constants';

interface NarratorReframeProps {
  startFrame: number;
}

/**
 * The narrator's reframe text that slides up from below with a
 * horizontal rule above it. "economics" pulses in blue.
 */
export const NarratorReframe: React.FC<NarratorReframeProps> = ({
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  // Horizontal rule: draws from center outward
  const ruleProgress = interpolate(
    localFrame,
    [0, TIMING.ruleDrawDuration],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateRight: 'clamp',
    }
  );
  const ruleWidth = 200 * ruleProgress;

  // Text slide-up
  const slideY = interpolate(
    localFrame,
    [0, TIMING.reframeSlideDuration],
    [TIMING.reframeSlideDistance, 0],
    {
      easing: Easing.out(Easing.cubic),
      extrapolateRight: 'clamp',
    }
  );

  const textOpacity = interpolate(
    localFrame,
    [0, TIMING.reframeSlideDuration],
    [0, 0.6],
    {
      easing: Easing.out(Easing.cubic),
      extrapolateRight: 'clamp',
    }
  );

  // "economics" pulse: starts at frame 260 absolute = localFrame 50 (210+50=260)
  const pulseLocalStart = TIMING.economicsPulseStart - startFrame;
  const pulseProgress = interpolate(
    localFrame,
    [pulseLocalStart, pulseLocalStart + TIMING.economicsPulseDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  // Pulse scale: 1.0 -> 1.08 -> 1.0 (use sine easing for smooth in-out)
  const pulseScale =
    pulseProgress > 0 && pulseProgress < 1
      ? 1 + (TIMING.economicsPulseScale - 1) * Math.sin(pulseProgress * Math.PI)
      : 1;

  // Pulse opacity: brighten during pulse
  const pulseOpacityBoost =
    pulseProgress > 0 && pulseProgress < 1
      ? 0.2 * Math.sin(pulseProgress * Math.PI)
      : 0;

  const economicsOpacity = 0.8 + pulseOpacityBoost;

  const baseTextStyle: React.CSSProperties = {
    fontFamily: 'Inter, sans-serif',
    fontSize: 18,
    fontWeight: 600,
    color: COLORS.reframeText,
    opacity: textOpacity,
  };

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        right: 0,
        top: 700,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        transform: `translateY(${slideY}px)`,
      }}
    >
      {/* Horizontal rule */}
      <div
        style={{
          width: ruleWidth,
          height: 1,
          backgroundColor: COLORS.ruleLine,
          opacity: 0.15,
          marginBottom: 16,
        }}
      />

      {/* Reframe text */}
      <div
        style={{
          textAlign: 'center',
          maxWidth: 800,
        }}
      >
        <span style={baseTextStyle}>
          {"He's right — it's a contrarian bet. But the "}
        </span>
        <span
          style={{
            ...baseTextStyle,
            color: COLORS.highlightBlue,
            opacity: economicsOpacity * (textOpacity / 0.6),
            display: 'inline-block',
            transform: `scale(${pulseScale})`,
          }}
        >
          economics
        </span>
        <span style={baseTextStyle}>{' are on our side.'}</span>
      </div>
    </div>
  );
};

export default NarratorReframe;
