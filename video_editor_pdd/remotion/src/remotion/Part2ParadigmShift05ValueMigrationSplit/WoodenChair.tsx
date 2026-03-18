import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CHAIR_CENTER,
  CHAIR_SIZE,
  WOOD_BODY,
  WOOD_GRAIN,
  CRAFT_ACCENT,
  PHASE_2_START,
  OUTLINE_DRAW_DURATION,
  PHASE_3_START,
  PHASE_3_END,
  CHISEL_STAGGER,
} from './constants';

/**
 * Simplified wooden chair with draw-on animation, chisel marks, and history labels.
 */
export const WoodenChair: React.FC = () => {
  const frame = useCurrentFrame();

  // Draw progress: chair outline draws from frame 20 to 60
  const drawProgress = interpolate(
    frame,
    [PHASE_2_START, PHASE_2_START + OUTLINE_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  // Chair SVG path total length (approximate)
  const chairPathLength = 1600;
  const chairStrokeDashoffset = chairPathLength * (1 - drawProgress);

  // Chisel marks: start appearing at frame 20, accumulate through frame 160
  const totalMarks = 47;
  const visibleMarks = Math.min(
    totalMarks,
    Math.max(0, Math.floor((frame - PHASE_2_START) / CHISEL_STAGGER))
  );

  // History labels: appear from frame 80 to 160
  const historyCount = Math.min(
    12,
    Math.max(0, Math.floor((frame - PHASE_3_START) / 6))
  );

  // Generate deterministic chisel marks
  const chiselMarks = React.useMemo(() => {
    const marks: { x: number; y: number; angle: number; len: number }[] = [];
    for (let i = 0; i < totalMarks; i++) {
      const seed = i * 137.508; // golden angle for distribution
      const x = CHAIR_CENTER.x - 100 + ((seed * 7) % 200);
      const y = CHAIR_CENTER.y - 150 + ((seed * 3) % 300);
      const angle = ((seed * 11) % 360);
      const len = 8 + ((seed * 5) % 12);
      marks.push({ x, y, angle, len });
    }
    return marks;
  }, []);

  return (
    <div style={{ position: 'absolute', top: 0, left: 0, width: '100%', height: '100%' }}>
      {/* Chair SVG */}
      <svg
        width={CHAIR_SIZE.w}
        height={CHAIR_SIZE.h}
        viewBox="0 0 300 400"
        style={{
          position: 'absolute',
          left: CHAIR_CENTER.x - CHAIR_SIZE.w / 2,
          top: CHAIR_CENTER.y - CHAIR_SIZE.h / 2,
          overflow: 'visible',
        }}
      >
        {/* Chair body - simplified vector */}
        {/* Seat */}
        <rect x="50" y="180" width="200" height="20" rx="3"
          fill={WOOD_BODY}
          stroke={WOOD_BODY}
          strokeWidth={2}
          strokeDasharray={chairPathLength}
          strokeDashoffset={chairStrokeDashoffset}
          opacity={drawProgress > 0.01 ? 1 : 0}
        />
        {/* Back rest */}
        <path
          d="M70,180 L70,40 Q150,20 230,40 L230,180"
          fill="none"
          stroke={WOOD_BODY}
          strokeWidth={3}
          strokeDasharray={chairPathLength}
          strokeDashoffset={chairStrokeDashoffset}
          opacity={drawProgress > 0.01 ? 1 : 0}
        />
        {/* Back slats */}
        <line x1="110" y1="60" x2="110" y2="175" stroke={WOOD_BODY} strokeWidth={2}
          strokeDasharray={chairPathLength} strokeDashoffset={chairStrokeDashoffset}
          opacity={drawProgress > 0.1 ? 1 : 0} />
        <line x1="150" y1="50" x2="150" y2="175" stroke={WOOD_BODY} strokeWidth={2}
          strokeDasharray={chairPathLength} strokeDashoffset={chairStrokeDashoffset}
          opacity={drawProgress > 0.1 ? 1 : 0} />
        <line x1="190" y1="60" x2="190" y2="175" stroke={WOOD_BODY} strokeWidth={2}
          strokeDasharray={chairPathLength} strokeDashoffset={chairStrokeDashoffset}
          opacity={drawProgress > 0.1 ? 1 : 0} />
        {/* Front legs */}
        <line x1="70" y1="200" x2="55" y2="380" stroke={WOOD_BODY} strokeWidth={4}
          strokeDasharray={chairPathLength} strokeDashoffset={chairStrokeDashoffset}
          opacity={drawProgress > 0.3 ? 1 : 0} />
        <line x1="230" y1="200" x2="245" y2="380" stroke={WOOD_BODY} strokeWidth={4}
          strokeDasharray={chairPathLength} strokeDashoffset={chairStrokeDashoffset}
          opacity={drawProgress > 0.3 ? 1 : 0} />
        {/* Back legs */}
        <line x1="85" y1="200" x2="75" y2="370" stroke={WOOD_BODY} strokeWidth={3}
          strokeDasharray={chairPathLength} strokeDashoffset={chairStrokeDashoffset}
          opacity={drawProgress > 0.4 ? 1 : 0} />
        <line x1="215" y1="200" x2="225" y2="370" stroke={WOOD_BODY} strokeWidth={3}
          strokeDasharray={chairPathLength} strokeDashoffset={chairStrokeDashoffset}
          opacity={drawProgress > 0.4 ? 1 : 0} />
        {/* Cross brace */}
        <line x1="65" y1="310" x2="240" y2="310" stroke={WOOD_BODY} strokeWidth={2}
          strokeDasharray={chairPathLength} strokeDashoffset={chairStrokeDashoffset}
          opacity={drawProgress > 0.5 ? 1 : 0} />

        {/* Wood grain texture lines */}
        {drawProgress > 0.6 && (
          <>
            <line x1="80" y1="185" x2="220" y2="185" stroke={WOOD_GRAIN} strokeWidth={0.5} opacity={0.1} />
            <line x1="90" y1="190" x2="210" y2="190" stroke={WOOD_GRAIN} strokeWidth={0.5} opacity={0.1} />
            <line x1="120" y1="80" x2="120" y2="170" stroke={WOOD_GRAIN} strokeWidth={0.5} opacity={0.1} />
            <line x1="180" y1="75" x2="180" y2="170" stroke={WOOD_GRAIN} strokeWidth={0.5} opacity={0.1} />
          </>
        )}
      </svg>

      {/* Chisel marks */}
      <svg
        width={CHAIR_SIZE.w + 40}
        height={CHAIR_SIZE.h + 40}
        viewBox="-20 -20 340 440"
        style={{
          position: 'absolute',
          left: CHAIR_CENTER.x - CHAIR_SIZE.w / 2 - 20,
          top: CHAIR_CENTER.y - CHAIR_SIZE.h / 2 - 20,
          overflow: 'visible',
        }}
      >
        {chiselMarks.slice(0, visibleMarks).map((mark, i) => {
          const markOpacity = interpolate(
            frame,
            [PHASE_2_START + i * CHISEL_STAGGER, PHASE_2_START + i * CHISEL_STAGGER + 5],
            [0, 0.3],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
          );
          const rad = (mark.angle * Math.PI) / 180;
          const dx = Math.cos(rad) * mark.len / 2;
          const dy = Math.sin(rad) * mark.len / 2;
          // Remap to chair-local coords
          const cx = mark.x - CHAIR_CENTER.x + CHAIR_SIZE.w / 2 + 20;
          const cy = mark.y - CHAIR_CENTER.y + CHAIR_SIZE.h / 2 + 20;
          return (
            <line
              key={i}
              x1={cx - dx}
              y1={cy - dy}
              x2={cx + dx}
              y2={cy + dy}
              stroke={WOOD_GRAIN}
              strokeWidth={1}
              opacity={markOpacity}
            />
          );
        })}
      </svg>

      {/* History labels — stacked near the chair */}
      {historyCount > 0 && (
        <div
          style={{
            position: 'absolute',
            left: CHAIR_CENTER.x + CHAIR_SIZE.w / 2 + 20,
            top: CHAIR_CENTER.y - 120,
            display: 'flex',
            flexDirection: 'column',
            gap: 2,
          }}
        >
          {Array.from({ length: historyCount }).map((_, i) => {
            const labelOpacity = interpolate(
              frame,
              [PHASE_3_START + i * 6, PHASE_3_START + i * 6 + 8],
              [0, 0.2],
              { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
            );
            return (
              <span
                key={i}
                style={{
                  fontFamily: 'JetBrains Mono, monospace',
                  fontSize: 8,
                  color: CRAFT_ACCENT,
                  opacity: labelOpacity,
                  whiteSpace: 'nowrap',
                }}
              >
                cut {i + 1}
              </span>
            );
          })}
        </div>
      )}
    </div>
  );
};

export default WoodenChair;
