import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  MOLD_CENTER,
  MOLD_SIZE,
  MOLD_ACCENT,
  MOLD_CAVITY,
  PLASTIC_COLOR,
  DISPOSABLE_LABEL_COLOR,
  PLASTIC_CENTER,
  PHASE_2_START,
  OUTLINE_DRAW_DURATION,
  PHASE_3_START,
  PHASE_3_END,
  PHASE_5_START,
  DISSOLVE_DURATION,
  REGEN_DURATION,
} from './constants';

/**
 * Injection mold cross-section with plastic part below.
 * Includes flow animation and dissolve/regenerate cycle.
 */
export const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  // Draw progress: mold outline draws from frame 20 to 60
  const drawProgress = interpolate(
    frame,
    [PHASE_2_START, PHASE_2_START + OUTLINE_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  const moldPathLength = 1200;
  const moldStrokeDashoffset = moldPathLength * (1 - drawProgress);

  // Plastic flow into mold: frame 80-130
  const plasticFlowProgress = interpolate(
    frame,
    [PHASE_3_START, PHASE_3_START + 50],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Part ejects below mold: frame 130-160
  const partEjectProgress = interpolate(
    frame,
    [PHASE_3_START + 50, PHASE_3_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Part dissolve: frame 240-260
  const dissolveProgress = interpolate(
    frame,
    [PHASE_5_START, PHASE_5_START + DISSOLVE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.quad) }
  );

  // Part regenerate: frame 265-280
  const regenProgress = interpolate(
    frame,
    [PHASE_5_START + DISSOLVE_DURATION + 5, PHASE_5_START + DISSOLVE_DURATION + 5 + REGEN_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Determine part opacity
  let partOpacity = 0;
  if (frame >= PHASE_3_START + 50 && frame < PHASE_5_START) {
    // Part has been ejected, visible
    partOpacity = partEjectProgress * 0.4;
  } else if (frame >= PHASE_5_START && frame < PHASE_5_START + DISSOLVE_DURATION) {
    // Dissolving
    partOpacity = 0.4 * (1 - dissolveProgress);
  } else if (frame >= PHASE_5_START + DISSOLVE_DURATION + 5) {
    // Regenerating
    partOpacity = regenProgress * 0.4;
  }

  // Particle scatter positions during dissolve
  const particles = React.useMemo(() => {
    const pts: { id: number; baseX: number; baseY: number; dx: number; dy: number }[] = [];
    for (let i = 0; i < 24; i++) {
      const angle = (i / 24) * Math.PI * 2 + (i * 0.3);
      const dist = 30 + (i * 7) % 60;
      pts.push({
        id: i,
        baseX: MOLD_CENTER.x - 60 + (i * 17) % 120,
        baseY: PLASTIC_CENTER.y - 30 + (i * 11) % 60,
        dx: Math.cos(angle) * dist,
        dy: Math.sin(angle) * dist,
      });
    }
    return pts;
  }, []);

  const showDissolveParticles = frame >= PHASE_5_START && frame < PHASE_5_START + DISSOLVE_DURATION + 5;

  return (
    <div style={{ position: 'absolute', top: 0, left: 0, width: '100%', height: '100%' }}>
      {/* Mold cross-section SVG */}
      <svg
        width={MOLD_SIZE.w}
        height={MOLD_SIZE.h}
        viewBox="0 0 300 250"
        style={{
          position: 'absolute',
          left: MOLD_CENTER.x - MOLD_SIZE.w / 2,
          top: MOLD_CENTER.y - MOLD_SIZE.h / 2,
          overflow: 'visible',
        }}
      >
        {/* Outer mold walls */}
        <path
          d="M20,10 L20,240 L130,240 L130,180 L170,180 L170,240 L280,240 L280,10 Z"
          fill="none"
          stroke={MOLD_ACCENT}
          strokeWidth={3}
          opacity={0.5}
          strokeDasharray={moldPathLength}
          strokeDashoffset={moldStrokeDashoffset}
        />
        {/* Inner cavity */}
        <path
          d="M50,30 L50,180 L130,180 L130,100 L170,100 L170,180 L250,180 L250,30 Z"
          fill={MOLD_CAVITY}
          opacity={drawProgress > 0.3 ? 0.3 : 0}
          stroke="none"
        />
        {/* Injection channel */}
        <rect
          x="140" y="0" width="20" height="30"
          fill={MOLD_CAVITY}
          opacity={drawProgress > 0.5 ? 0.3 : 0}
        />
        {/* Plastic flowing into cavity */}
        {plasticFlowProgress > 0 && (
          <rect
            x="50" y={180 - plasticFlowProgress * 150}
            width="200"
            height={plasticFlowProgress * 150}
            fill={PLASTIC_COLOR}
            opacity={0.25}
            rx={2}
          />
        )}
      </svg>

      {/* Ejected plastic part */}
      {partOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            left: MOLD_CENTER.x - 100,
            top: PLASTIC_CENTER.y - 30,
            width: 200,
            height: 60,
            backgroundColor: PLASTIC_COLOR,
            opacity: partOpacity,
            borderRadius: 4,
          }}
        >
          {/* "disposable" label */}
          <span
            style={{
              position: 'absolute',
              bottom: -18,
              left: '50%',
              transform: 'translateX(-50%)',
              fontFamily: 'Inter, sans-serif',
              fontSize: 9,
              color: DISPOSABLE_LABEL_COLOR,
              opacity: 0.3,
              whiteSpace: 'nowrap',
            }}
          >
            disposable
          </span>
        </div>
      )}

      {/* Dissolve particles */}
      {showDissolveParticles && (
        <svg
          width="400"
          height="200"
          style={{
            position: 'absolute',
            left: MOLD_CENTER.x - 200,
            top: PLASTIC_CENTER.y - 80,
            overflow: 'visible',
            pointerEvents: 'none',
          }}
        >
          {particles.map((p) => {
            const pOpacity = interpolate(
              dissolveProgress,
              [0, 0.5, 1],
              [0, 0.4, 0],
              { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
            );
            const px = (p.baseX - MOLD_CENTER.x + 200) + p.dx * dissolveProgress;
            const py = (p.baseY - PLASTIC_CENTER.y + 80) + p.dy * dissolveProgress;
            return (
              <circle
                key={p.id}
                cx={px}
                cy={py}
                r={2 + (p.id % 3)}
                fill={PLASTIC_COLOR}
                opacity={pOpacity}
              />
            );
          })}
        </svg>
      )}
    </div>
  );
};

export default MoldCrossSection;
