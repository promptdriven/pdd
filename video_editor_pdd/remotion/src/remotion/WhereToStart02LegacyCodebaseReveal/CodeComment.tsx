import React, { useMemo } from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { ANNOTATION_COLOR } from './constants';

interface CodeCommentProps {
  text: string;
  x: number;
  y: number;
  opacity: number;
  startFrame: number;
  fadeDuration?: number;
  jitter?: number;
}

// Seeded random for deterministic jitter per annotation
function seededJitter(seed: number): { dx: number; dy: number } {
  const s1 = ((seed * 9301 + 49297) % 233280) / 233280;
  const s2 = ((seed * 7927 + 13849) % 233280) / 233280;
  return {
    dx: (s1 - 0.5) * 2,
    dy: (s2 - 0.5) * 2,
  };
}

export const CodeComment: React.FC<CodeCommentProps> = ({
  text,
  x,
  y,
  opacity: targetOpacity,
  startFrame,
  fadeDuration = 12,
  jitter = 2,
}) => {
  const frame = useCurrentFrame();

  // Deterministic jitter offset based on text hash
  const jitterOffset = useMemo(() => {
    let hash = 0;
    for (let i = 0; i < text.length; i++) {
      hash = ((hash << 5) - hash) + text.charCodeAt(i);
      hash |= 0;
    }
    return seededJitter(Math.abs(hash));
  }, [text]);

  // Fade in with easeOut(quad)
  const fadeProgress = interpolate(
    frame,
    [startFrame, startFrame + fadeDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Jitter animates during the fade-in, then settles
  const jitterProgress = interpolate(
    frame,
    [startFrame, startFrame + fadeDuration],
    [1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const offsetX = jitterOffset.dx * jitter * jitterProgress;
  const offsetY = jitterOffset.dy * jitter * jitterProgress;

  if (fadeProgress <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: x + offsetX,
        top: y + offsetY,
        fontFamily: '"JetBrains Mono", "Fira Code", "Courier New", monospace',
        fontSize: 10,
        fontStyle: 'italic',
        color: ANNOTATION_COLOR,
        opacity: targetOpacity * fadeProgress,
        whiteSpace: 'nowrap',
        pointerEvents: 'none',
        textShadow: `0 0 6px rgba(239, 68, 68, ${0.3 * fadeProgress})`,
      }}
    >
      {text}
    </div>
  );
};
