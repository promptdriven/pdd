import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  BLOCK_FILL_CLEAN,
  BLOCK_FILL_DEBT,
  BLOCK_BORDER_OPACITY,
  DEBT_GLOW_OPACITY,
  type BlockDef,
} from './constants';

interface CodeBlockProps {
  block: BlockDef;
  staggerDelay: number;
}

export const CodeBlock: React.FC<CodeBlockProps> = ({ block, staggerDelay }) => {
  const frame = useCurrentFrame();

  // Fade in from center outward, staggered by cluster then index
  const appearProgress = interpolate(
    frame,
    [staggerDelay, staggerDelay + 15],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Red tint accumulation on debt blocks (frame 30-50)
  const debtTintProgress = block.hasDebt
    ? interpolate(
        frame,
        [30, 50],
        [0, 1],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
      )
    : 0;

  // Interpolate fill color between clean and debt
  const fillColor = block.hasDebt
    ? lerpColor(BLOCK_FILL_CLEAN, BLOCK_FILL_DEBT, debtTintProgress)
    : BLOCK_FILL_CLEAN;

  const scale = interpolate(appearProgress, [0, 1], [0.6, 1]);

  return (
    <div
      style={{
        position: 'absolute',
        left: block.x,
        top: block.y,
        width: block.w,
        height: block.h,
        backgroundColor: fillColor,
        border: `1px solid rgba(51, 65, 85, ${BLOCK_BORDER_OPACITY})`,
        borderRadius: 3,
        opacity: appearProgress,
        transform: `scale(${scale})`,
        boxShadow: block.hasDebt && debtTintProgress > 0
          ? `0 0 ${8 * debtTintProgress}px rgba(217, 148, 74, ${DEBT_GLOW_OPACITY * debtTintProgress})`
          : 'none',
      }}
    />
  );
};

// Simple hex color interpolation
function lerpColor(a: string, b: string, t: number): string {
  const parseHex = (hex: string) => {
    const h = hex.replace('#', '');
    return [
      parseInt(h.substring(0, 2), 16),
      parseInt(h.substring(2, 4), 16),
      parseInt(h.substring(4, 6), 16),
    ];
  };
  const [ar, ag, ab] = parseHex(a);
  const [br, bg, bb] = parseHex(b);
  const r = Math.round(ar + (br - ar) * t);
  const g = Math.round(ag + (bg - ag) * t);
  const bv = Math.round(ab + (bb - ab) * t);
  return `rgb(${r}, ${g}, ${bv})`;
}
