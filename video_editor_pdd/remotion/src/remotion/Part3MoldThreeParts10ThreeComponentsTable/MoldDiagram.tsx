import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { AMBER, BLUE, GREEN, TEXT_PRIMARY, TIMING } from './constants';

/**
 * MoldDiagram — renders the cross-section mold with three glowing regions
 * and a flow animation (text particles → grounding → walls → code output).
 * Slides left and shrinks at TIMING.MOLD_SLIDE_START.
 */
export const MoldDiagram: React.FC = () => {
  const frame = useCurrentFrame();

  // Slide + scale transition
  const slideProgress = interpolate(
    frame,
    [TIMING.MOLD_SLIDE_START, TIMING.MOLD_SLIDE_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  const centerX = interpolate(slideProgress, [0, 1], [960, 350]);
  const centerY = 500;
  const scale = interpolate(slideProgress, [0, 1], [1, 0.5]);

  // Flow animation — cycles through phases
  const flowPhase = interpolate(
    frame % 90,
    [0, 30, 60, 90],
    [0, 1, 2, 3],
    { extrapolateRight: 'clamp' }
  );

  // Glow pulse for all regions
  const glowPulse = interpolate(
    Math.sin(frame * 0.08),
    [-1, 1],
    [0.6, 1.0]
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: centerX,
        top: centerY,
        transform: `translate(-50%, -50%) scale(${scale})`,
        width: 400,
        height: 600,
        transformOrigin: 'center center',
      }}
    >
      <svg width={400} height={600} viewBox="0 0 400 600">
        {/* Glow filters */}
        <defs>
          <filter id="glow-amber" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="6" result="blur" />
            <feComposite in="SourceGraphic" in2="blur" operator="over" />
          </filter>
          <filter id="glow-blue" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="6" result="blur" />
            <feComposite in="SourceGraphic" in2="blur" operator="over" />
          </filter>
          <filter id="glow-green" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="6" result="blur" />
            <feComposite in="SourceGraphic" in2="blur" operator="over" />
          </filter>
        </defs>

        {/* Mold outline */}
        <rect
          x={20}
          y={20}
          width={360}
          height={560}
          rx={8}
          fill="none"
          stroke="#334155"
          strokeWidth={1}
          opacity={0.3}
        />

        {/* Amber walls (left + right) */}
        <rect
          x={20}
          y={100}
          width={50}
          height={400}
          fill={AMBER}
          opacity={0.25 * glowPulse}
          filter="url(#glow-amber)"
        />
        <rect
          x={330}
          y={100}
          width={50}
          height={400}
          fill={AMBER}
          opacity={0.25 * glowPulse}
          filter="url(#glow-amber)"
        />
        {/* Wall inner edges */}
        <line x1={70} y1={100} x2={70} y2={500} stroke={AMBER} strokeWidth={2} opacity={0.7 * glowPulse} />
        <line x1={330} y1={100} x2={330} y2={500} stroke={AMBER} strokeWidth={2} opacity={0.7 * glowPulse} />
        {/* Wall labels */}
        <text x={45} y={300} fill={AMBER} fontSize={11} fontFamily="Inter" fontWeight={600} opacity={0.6}
          textAnchor="middle" transform="rotate(-90, 45, 300)">
          TESTS
        </text>
        <text x={355} y={300} fill={AMBER} fontSize={11} fontFamily="Inter" fontWeight={600} opacity={0.6}
          textAnchor="middle" transform="rotate(90, 355, 300)">
          TESTS
        </text>

        {/* Blue nozzle (top) */}
        <path
          d="M 160 20 L 240 20 L 220 100 L 180 100 Z"
          fill={BLUE}
          opacity={0.3 * glowPulse}
          filter="url(#glow-blue)"
        />
        <path
          d="M 160 20 L 240 20 L 220 100 L 180 100 Z"
          fill="none"
          stroke={BLUE}
          strokeWidth={1.5}
          opacity={0.8 * glowPulse}
        />
        <text x={200} y={65} fill={BLUE} fontSize={11} fontFamily="Inter" fontWeight={600} opacity={0.7}
          textAnchor="middle">
          PROMPT
        </text>

        {/* Green cavity (center) */}
        <rect
          x={80}
          y={140}
          width={240}
          height={280}
          rx={6}
          fill={GREEN}
          opacity={0.12 * glowPulse}
          filter="url(#glow-green)"
        />
        <rect
          x={80}
          y={140}
          width={240}
          height={280}
          rx={6}
          fill="none"
          stroke={GREEN}
          strokeWidth={1}
          opacity={0.5 * glowPulse}
        />
        <text x={200} y={290} fill={GREEN} fontSize={11} fontFamily="Inter" fontWeight={600} opacity={0.5}
          textAnchor="middle">
          GROUNDING
        </text>

        {/* Flow particles */}
        {frame < TIMING.MOLD_SLIDE_END && (
          <>
            {/* Input text particles entering nozzle */}
            {[0, 20, 40, 60].map((offset) => {
              const p = ((frame + offset) % 90) / 90;
              const py = interpolate(p, [0, 0.15, 0.3, 0.85, 1], [30, 100, 160, 420, 530]);
              const px = 200 + Math.sin(p * Math.PI * 3) * 15;
              const particleOpacity = p < 0.15 ? 0.6 : p < 0.3 ? 0.5 : 0.4;
              const particleColor = p < 0.15 ? BLUE : p < 0.85 ? GREEN : TEXT_PRIMARY;
              return (
                <circle
                  key={`p-${offset}`}
                  cx={px}
                  cy={py}
                  r={3}
                  fill={particleColor}
                  opacity={particleOpacity}
                />
              );
            })}

            {/* Wall flash when particles near walls */}
            {flowPhase > 1.5 && (
              <>
                <rect x={70} y={250} width={3} height={40} fill={AMBER}
                  opacity={interpolate(flowPhase, [1.5, 2, 2.5], [0, 0.6, 0], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })} />
                <rect x={327} y={250} width={3} height={40} fill={AMBER}
                  opacity={interpolate(flowPhase, [1.5, 2, 2.5], [0, 0.6, 0], { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' })} />
              </>
            )}
          </>
        )}

        {/* Output code area (bottom) */}
        <rect
          x={100}
          y={500}
          width={200}
          height={60}
          rx={4}
          fill="#0F172A"
          opacity={0.6}
        />
        <text x={200} y={535} fill={TEXT_PRIMARY} fontSize={9} fontFamily="JetBrains Mono, monospace" opacity={0.5}
          textAnchor="middle">
          {'{ code output }'}
        </text>
      </svg>
    </div>
  );
};
