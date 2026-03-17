import React from 'react';
import { useCurrentFrame, interpolate, Easing, spring, useVideoConfig, AbsoluteFill } from 'remotion';
import { COLORS, TIMING } from './constants';

// Typewriter effect for proof notation
const TypewriterText: React.FC<{
  text: string;
  startFrame: number;
  charDelay: number;
  style: React.CSSProperties;
}> = ({ text, startFrame, charDelay, style }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;
  if (localFrame < 0) return null;

  const charsVisible = Math.floor(localFrame / charDelay);
  const visibleText = text.substring(0, Math.min(charsVisible, text.length));
  const showCursor = charsVisible < text.length && localFrame % 6 < 3;

  return (
    <div style={style}>
      {visibleText}
      {showCursor && (
        <span style={{ opacity: 0.7 }}>▌</span>
      )}
    </div>
  );
};

// Logo placeholder (text-based since we don't have SVG files)
const LogoPlaceholder: React.FC<{
  label: string;
  x: number;
  y: number;
  opacity: number;
}> = ({ label, x, y, opacity }) => (
  <div
    style={{
      position: 'absolute',
      left: x,
      top: y,
      width: 120,
      height: 60,
      display: 'flex',
      alignItems: 'center',
      justifyContent: 'center',
      border: `1px solid ${COLORS.textSecondary}`,
      borderRadius: 8,
      opacity,
      color: COLORS.textSecondary,
      fontFamily: 'Inter, sans-serif',
      fontSize: 14,
      fontWeight: 600,
      letterSpacing: 1,
    }}
  >
    {label}
  </div>
);

export const ProofSection: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // This component receives frames relative to beat 2 start (frame 300 globally)
  // But since we're called from a Sequence with from={300}, useCurrentFrame() is local.
  // Actually, we're inside the main component, so frame is global.
  // We'll use global frame references from TIMING.

  // Cross-dissolve: fade in the dark overlay
  const dissolveOpacity = interpolate(
    frame,
    [TIMING.beat2Start, TIMING.beat2Start + TIMING.crossDissolveDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
  );

  // Logo fade
  const logoOpacity = interpolate(
    frame,
    [TIMING.logoStart, TIMING.logoStart + 20],
    [0, 0.5],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Proof line 1
  const line1Opacity = interpolate(
    frame,
    [TIMING.proofLine1Start, TIMING.proofLine1Start + 10],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Proof line 2
  const line2Opacity = interpolate(
    frame,
    [TIMING.proofLine2Start, TIMING.proofLine2Start + 10],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Proof steps
  const stepsOpacity = interpolate(
    frame,
    [TIMING.proofStepsStart, TIMING.proofStepsStart + 15],
    [0, 0.5],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // PROVEN stamp spring animation
  const stampSpring = spring({
    frame: Math.max(0, frame - TIMING.stampStart),
    fps,
    config: { stiffness: 300, damping: 8 },
  });
  const stampScale = interpolate(stampSpring, [0, 1], [1.5, 1], { extrapolateRight: 'clamp' });
  const stampOpacity = interpolate(
    frame,
    [TIMING.stampStart, TIMING.stampStart + 4],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Green flash on stamp
  const flashOpacity = interpolate(
    frame,
    [TIMING.stampStart, TIMING.stampStart + 6, TIMING.stampStart + 20],
    [0, 0.3, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Annotation fade
  const annotationOpacity = interpolate(
    frame,
    [TIMING.annotationStart, TIMING.annotationStart + 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  if (frame < TIMING.beat2Start) return null;

  return (
    <AbsoluteFill style={{ opacity: dissolveOpacity }}>
      <AbsoluteFill style={{ backgroundColor: COLORS.bgDarker }} />

      {/* Subtle grid for beat 2 */}
      <AbsoluteFill style={{ opacity: 0.02 }}>
        <svg width={1920} height={1080}>
          {Array.from({ length: 20 }).map((_, i) => (
            <line
              key={`h${i}`}
              x1={0} y1={i * 60} x2={1920} y2={i * 60}
              stroke={COLORS.gridDot}
              strokeWidth={0.5}
            />
          ))}
          {Array.from({ length: 33 }).map((_, i) => (
            <line
              key={`v${i}`}
              x1={i * 60} y1={0} x2={i * 60} y2={1080}
              stroke={COLORS.gridDot}
              strokeWidth={0.5}
            />
          ))}
        </svg>
      </AbsoluteFill>

      {/* Logos */}
      <LogoPlaceholder label="Z3" x={750} y={160} opacity={logoOpacity} />
      <LogoPlaceholder label="Synopsys" x={1050} y={160} opacity={logoOpacity} />

      {/* Connecting label */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          right: 0,
          top: 235,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 13,
          color: COLORS.textMuted,
          opacity: logoOpacity,
          letterSpacing: 0.5,
        }}
      >
        Same class of SMT solver used in chip verification
      </div>

      {/* Proof notation line 1 */}
      <div style={{ opacity: line1Opacity }}>
        <TypewriterText
          text="∀ input ∈ String:"
          startFrame={TIMING.proofLine1Start}
          charDelay={3}
          style={{
            position: 'absolute',
            left: 0,
            right: 0,
            top: 340,
            textAlign: 'center',
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 28,
            color: COLORS.proofPurple,
            letterSpacing: 1,
          }}
        />
      </div>

      {/* Proof notation line 2 */}
      <div style={{ opacity: line2Opacity }}>
        <TypewriterText
          text="parse(input) ∈ {Valid(id), None}"
          startFrame={TIMING.proofLine2Start}
          charDelay={2}
          style={{
            position: 'absolute',
            left: 0,
            right: 0,
            top: 400,
            textAlign: 'center',
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 22,
            color: COLORS.proofBlue,
            letterSpacing: 0.5,
          }}
        />
      </div>

      {/* Proof steps */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          right: 0,
          top: 460,
          textAlign: 'center',
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: 14,
          color: COLORS.textSecondary,
          opacity: stepsOpacity,
          lineHeight: '24px',
        }}
      >
        <div>1. Enumerate all branches of parse()</div>
        <div>2. Verify each branch → Valid(id) | None</div>
        <div>3. No third outcome exists ∎</div>
      </div>

      {/* Green flash overlay */}
      {flashOpacity > 0 && (
        <AbsoluteFill
          style={{
            backgroundColor: COLORS.pass,
            opacity: flashOpacity,
          }}
        />
      )}

      {/* PROVEN stamp */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          right: 0,
          top: 560,
          display: 'flex',
          justifyContent: 'center',
          opacity: stampOpacity,
        }}
      >
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 40,
            fontWeight: 700,
            color: COLORS.pass,
            border: `3px solid ${COLORS.pass}`,
            borderRadius: 8,
            padding: '8px 32px',
            transform: `scale(${stampScale}) rotate(-5deg)`,
            letterSpacing: 3,
            textShadow: `0 0 20px ${COLORS.pass}`,
          }}
        >
          PROVEN ✓
        </div>
      </div>

      {/* Annotation */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          right: 0,
          top: 700,
          textAlign: 'center',
          opacity: annotationOpacity,
        }}
      >
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 18,
            fontWeight: 700,
            color: COLORS.textPrimary,
            opacity: 0.8,
          }}
        >
          Not sampling. Mathematical proof.
        </div>
        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            color: COLORS.textAccent,
            opacity: 0.6,
            marginTop: 12,
          }}
        >
          The chip design analogy isn't a metaphor. It's the same technology.
        </div>
      </div>
    </AbsoluteFill>
  );
};
