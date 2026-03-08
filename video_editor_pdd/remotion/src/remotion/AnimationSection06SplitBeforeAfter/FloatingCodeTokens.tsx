import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION_TIMING, CODE_TOKENS } from './constants';

interface TokenConfig {
  text: string;
  startX: number;
  startY: number;
  speed: number;
  delay: number;
}

const TOKEN_CONFIGS: TokenConfig[] = CODE_TOKENS.map((text, i) => ({
  text,
  startX: 80 + (i % 3) * 140,
  startY: 400 + i * 80,
  speed: 0.8 + (i * 0.3),
  delay: i * 4,
}));

export const FloatingCodeTokens: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <>
      {TOKEN_CONFIGS.map((token, i) => {
        const tokenStart = ANIMATION_TIMING.tokensStart + token.delay;

        const opacity = interpolate(
          frame,
          [tokenStart, tokenStart + 8],
          [0, 0.4],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );

        // Continuous upward drift (linear)
        const driftY = frame > tokenStart
          ? -(frame - tokenStart) * token.speed
          : 0;

        // Slight horizontal oscillation
        const driftX = frame > tokenStart
          ? Math.sin((frame - tokenStart) * 0.08 + i) * 10
          : 0;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: token.startX,
              top: token.startY,
              transform: `translate(${driftX}px, ${driftY}px)`,
              opacity,
              backgroundColor: COLORS.codeToken,
              borderRadius: 16,
              padding: '6px 14px',
              display: 'flex',
              alignItems: 'center',
              justifyContent: 'center',
            }}
          >
            <span
              style={{
                fontFamily: TYPOGRAPHY.codeToken.fontFamily,
                fontSize: TYPOGRAPHY.codeToken.fontSize,
                fontWeight: TYPOGRAPHY.codeToken.fontWeight,
                color: '#FFFFFF',
                whiteSpace: 'nowrap',
              }}
            >
              {token.text}
            </span>
          </div>
        );
      })}
    </>
  );
};
