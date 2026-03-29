import React from 'react';
import { useCurrentFrame, interpolate, Easing, spring } from 'remotion';
import {
  TERMINAL_BG,
  TERMINAL_TEXT,
  TERMINAL_BORDER_RADIUS,
  TERMINAL_WIDTH,
  TERMINAL_HEIGHT,
  TERMINAL_FONT_SIZE,
  TERMINAL_MARGIN,
  PHASE_TERMINAL_START,
  PHASE_TERMINAL_END,
} from './constants';

const FPS = 30;

/**
 * Bottom-right terminal overlay showing `$ pdd generate process_order ✓`.
 */
export const TerminalOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in over 10 frames (38-48)
  const opacity = interpolate(
    frame,
    [PHASE_TERMINAL_START, PHASE_TERMINAL_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Checkmark spring animation
  const checkScale = spring({
    frame: frame - PHASE_TERMINAL_START - 5,
    fps: FPS,
    config: {
      stiffness: 200,
      damping: 15,
    },
  });

  if (frame < PHASE_TERMINAL_START) return null;

  return (
    <div
      style={{
        position: 'absolute',
        bottom: TERMINAL_MARGIN,
        right: TERMINAL_MARGIN,
        width: TERMINAL_WIDTH,
        height: TERMINAL_HEIGHT,
        backgroundColor: TERMINAL_BG,
        opacity: opacity * 0.9,
        borderRadius: TERMINAL_BORDER_RADIUS,
        display: 'flex',
        alignItems: 'center',
        paddingLeft: 16,
        paddingRight: 16,
        fontFamily: '"JetBrains Mono", "Fira Code", monospace',
        fontSize: TERMINAL_FONT_SIZE,
        color: TERMINAL_TEXT,
        boxShadow: '0 4px 20px rgba(0,0,0,0.5)',
      }}
    >
      <span style={{ opacity: 0.6, marginRight: 8, color: '#585B70' }}>$</span>
      <span>pdd generate process_order</span>
      <span
        style={{
          marginLeft: 10,
          transform: `scale(${checkScale})`,
          display: 'inline-block',
          color: '#A6E3A1',
          fontWeight: 'bold',
        }}
      >
        ✓
      </span>
    </div>
  );
};

export default TerminalOverlay;
