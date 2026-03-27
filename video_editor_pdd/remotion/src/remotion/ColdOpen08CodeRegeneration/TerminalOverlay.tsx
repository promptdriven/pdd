import React from 'react';
import { useCurrentFrame, interpolate, Easing, spring } from 'remotion';

/**
 * Bottom-right terminal showing `$ pdd generate process_order ✓`.
 * Fades in over 10 frames with easeOut(quad); checkmark uses spring.
 */

interface TerminalOverlayProps {
  fadeInStartFrame: number;
  fadeInDuration: number;
  command: string;
  bgColor: string;
  bgOpacity: number;
  textColor: string;
  fontSize: number;
  width: number;
  height: number;
  right: number;
  bottom: number;
  borderRadius: number;
  fps: number;
}

export const TerminalOverlay: React.FC<TerminalOverlayProps> = ({
  fadeInStartFrame,
  fadeInDuration,
  command,
  bgColor,
  bgOpacity,
  textColor,
  fontSize,
  width,
  height,
  right,
  bottom,
  borderRadius,
  fps,
}) => {
  const frame = useCurrentFrame();

  // Container fade
  const containerOpacity = interpolate(
    frame,
    [fadeInStartFrame, fadeInStartFrame + fadeInDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  if (containerOpacity <= 0) return null;

  // Checkmark spring (appears slightly after text)
  const checkFrame = frame - (fadeInStartFrame + fadeInDuration - 2);
  const checkScale = spring({
    frame: Math.max(0, checkFrame),
    fps,
    config: { stiffness: 200, damping: 15 },
  });

  const checkOpacity = checkFrame >= 0 ? 1 : 0;

  return (
    <div
      style={{
        position: 'absolute',
        right,
        bottom,
        width,
        height,
        borderRadius,
        backgroundColor: bgColor,
        opacity: containerOpacity,
        display: 'flex',
        alignItems: 'center',
        paddingLeft: 16,
        paddingRight: 16,
        boxShadow: '0 4px 24px rgba(0,0,0,0.4)',
      }}
    >
      {/* Semi-transparent overlay for the bg */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          right: 0,
          bottom: 0,
          backgroundColor: bgColor,
          opacity: bgOpacity,
          borderRadius,
        }}
      />

      <span
        style={{
          position: 'relative',
          fontFamily: 'JetBrains Mono, monospace',
          fontSize,
          color: textColor,
          zIndex: 1,
          whiteSpace: 'nowrap',
        }}
      >
        {'$ '}
        {command}
        {' '}
        <span
          style={{
            display: 'inline-block',
            transform: `scale(${checkScale})`,
            opacity: checkOpacity,
            color: textColor,
          }}
        >
          ✓
        </span>
      </span>
    </div>
  );
};
