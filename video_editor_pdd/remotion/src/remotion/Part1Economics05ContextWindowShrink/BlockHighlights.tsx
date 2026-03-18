import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  GRID_AREA_SIZE,
  GAP,
  GRID_CENTER_X,
  GRID_CENTER_Y,
  COLOR_RED,
  COLOR_GREEN,
  RED_HIGHLIGHTS,
  GREEN_HIGHLIGHTS,
  HOLD_START,
  HIGHLIGHTS_START,
} from './constants';

const GRID_SIZE_32 = 32;
const BLOCK_SIZE_32 = (GRID_AREA_SIZE - (GRID_SIZE_32 - 1) * GAP) / GRID_SIZE_32;
const TOTAL_GRID = GRID_SIZE_32 * BLOCK_SIZE_32 + (GRID_SIZE_32 - 1) * GAP;
const GRID_LEFT = GRID_CENTER_X - TOTAL_GRID / 2;
const GRID_TOP = GRID_CENTER_Y - TOTAL_GRID / 2;

interface HighlightBlockProps {
  row: number;
  col: number;
  color: string;
  icon: string;
  delay: number;
  isPulsing: boolean;
  frame: number;
}

const HighlightBlock: React.FC<HighlightBlockProps> = ({
  row,
  col,
  color,
  icon,
  delay,
  isPulsing,
  frame,
}) => {
  const opacity = interpolate(frame - delay, [0, 10], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Pulse for green blocks outside window
  const pulseFrame = frame - delay;
  const glowOpacity = isPulsing && pulseFrame > 10
    ? interpolate(
        pulseFrame % 45,
        [0, 22, 45],
        [0.15, 0.25, 0.15],
        { easing: Easing.inOut(Easing.sin) }
      )
    : 0;

  const left = GRID_LEFT + col * (BLOCK_SIZE_32 + GAP);
  const top = GRID_TOP + row * (BLOCK_SIZE_32 + GAP);

  return (
    <div
      style={{
        position: 'absolute',
        left,
        top,
        width: BLOCK_SIZE_32,
        height: BLOCK_SIZE_32,
        backgroundColor: `${color}26`, // ~0.15 opacity
        border: `1px solid ${color}4D`, // ~0.3 opacity
        borderRadius: 2,
        opacity,
        boxShadow: isPulsing ? `0 0 6px ${color}${Math.round(glowOpacity * 255).toString(16).padStart(2, '0')}` : 'none',
        zIndex: 20,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
      }}
    >
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: Math.max(6, BLOCK_SIZE_32 * 0.5),
          color,
          opacity: 0.7,
        }}
      >
        {icon}
      </span>
    </div>
  );
};

export const BlockHighlights: React.FC = () => {
  const frame = useCurrentFrame();

  const isInHoldPhase = frame + HIGHLIGHTS_START >= HOLD_START;

  return (
    <>
      {/* Red highlights inside window — irrelevant code */}
      {RED_HIGHLIGHTS.map((pos, i) => (
        <HighlightBlock
          key={`red-${i}`}
          row={pos.row}
          col={pos.col}
          color={COLOR_RED}
          icon="✗"
          delay={i * 5}
          isPulsing={false}
          frame={frame}
        />
      ))}

      {/* Green highlights outside window — needed code */}
      {GREEN_HIGHLIGHTS.map((pos, i) => (
        <HighlightBlock
          key={`green-${i}`}
          row={pos.row}
          col={pos.col}
          color={COLOR_GREEN}
          icon="✓"
          delay={RED_HIGHLIGHTS.length * 5 + i * 5}
          isPulsing={isInHoldPhase}
          frame={frame}
        />
      ))}
    </>
  );
};

export default BlockHighlights;
