import React from 'react';
import { useCurrentFrame, Easing, interpolate, spring, useVideoConfig } from 'remotion';
import {
  FONT_MONO,
  FONT_SANS,
  COLOR_PASS,
  COLOR_PURPLE,
  COLOR_BLUE,
  COLOR_AMBER,
  TEXT_PRIMARY,
  TEXT_SECONDARY,
  TEXT_MUTED,
  PROOF_LINES,
  PROOF_STEPS,
  BG_DARK,
} from './constants';

// All frame offsets are relative to Beat 2 start (parent Sequence from={300})
const LOGOS_IN = 30;       // 330 absolute
const PROOF_IN = 90;       // 390 absolute
const STAMP_IN = 150;      // 450 absolute
const ANNOTATION_IN = 180; // 480 absolute

export const ProofSection: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Logo fade-in (frames 30-50 local)
  const logoOpacity = interpolate(
    frame,
    [LOGOS_IN, LOGOS_IN + 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Proof line 1 typewriter (frames 90+)
  const line1Chars = PROOF_LINES[0].text.length;
  const line1Progress = interpolate(
    frame,
    [PROOF_IN, PROOF_IN + line1Chars * 3],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const line1Visible = Math.floor(line1Progress * line1Chars);

  // Proof line 2 typewriter (frames 90+30 chars offset)
  const line2Start = PROOF_IN + 30;
  const line2Chars = PROOF_LINES[1].text.length;
  const line2Progress = interpolate(
    frame,
    [line2Start, line2Start + line2Chars * 2],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const line2Visible = Math.floor(line2Progress * line2Chars);

  // Proof steps fade
  const stepsOpacity = interpolate(
    frame,
    [PROOF_IN + 50, PROOF_IN + 70],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // PROVEN stamp spring
  const stampSpring = frame >= STAMP_IN
    ? spring({
        frame: frame - STAMP_IN,
        fps,
        config: { stiffness: 300, damping: 8 },
      })
    : 0;
  const stampScale = 1.5 - stampSpring * 0.5; // 1.5 -> 1.0
  const stampOpacity = Math.min(1, stampSpring * 2);

  // Green flash behind stamp
  const flashOpacity = frame >= STAMP_IN
    ? interpolate(
        frame,
        [STAMP_IN, STAMP_IN + 6, STAMP_IN + 20],
        [0, 0.3, 0],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
      )
    : 0;

  // Annotation fade
  const annotationOpacity = interpolate(
    frame,
    [ANNOTATION_IN, ANNOTATION_IN + 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        backgroundColor: BG_DARK,
      }}
    >
      {/* Logos section */}
      <div
        style={{
          position: 'absolute',
          top: 180,
          left: 0,
          width: 1920,
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'center',
          opacity: logoOpacity,
        }}
      >
        <div style={{ display: 'flex', alignItems: 'center', gap: 60 }}>
          {/* Z3 Logo (text-based) */}
          <div
            style={{
              display: 'flex',
              flexDirection: 'column',
              alignItems: 'center',
            }}
          >
            <div
              style={{
                width: 60,
                height: 60,
                borderRadius: 8,
                border: `2px solid ${TEXT_MUTED}50`,
                display: 'flex',
                alignItems: 'center',
                justifyContent: 'center',
                fontFamily: FONT_MONO,
                fontSize: 28,
                fontWeight: 700,
                color: TEXT_MUTED,
                opacity: 0.7,
              }}
            >
              Z3
            </div>
            <span
              style={{
                fontFamily: FONT_SANS,
                fontSize: 10,
                color: TEXT_MUTED,
                opacity: 0.5,
                marginTop: 6,
              }}
            >
              Z3 SMT Solver
            </span>
          </div>

          {/* Connecting line */}
          <div
            style={{
              width: 80,
              height: 2,
              backgroundColor: TEXT_MUTED,
              opacity: 0.2,
            }}
          />

          {/* Synopsys Formality Logo (text-based) */}
          <div
            style={{
              display: 'flex',
              flexDirection: 'column',
              alignItems: 'center',
            }}
          >
            <div
              style={{
                width: 60,
                height: 60,
                borderRadius: 8,
                border: `2px solid ${TEXT_MUTED}50`,
                display: 'flex',
                alignItems: 'center',
                justifyContent: 'center',
                fontFamily: FONT_SANS,
                fontSize: 11,
                fontWeight: 600,
                color: TEXT_MUTED,
                opacity: 0.7,
                textAlign: 'center',
                lineHeight: '13px',
              }}
            >
              SYN
            </div>
            <span
              style={{
                fontFamily: FONT_SANS,
                fontSize: 10,
                color: TEXT_MUTED,
                opacity: 0.5,
                marginTop: 6,
              }}
            >
              Synopsys Formality
            </span>
          </div>
        </div>

        {/* Connecting label */}
        <span
          style={{
            fontFamily: FONT_SANS,
            fontSize: 11,
            color: TEXT_SECONDARY,
            opacity: 0.5,
            marginTop: 16,
          }}
        >
          Same class of SMT solver used in chip verification
        </span>
      </div>

      {/* Proof notation */}
      <div
        style={{
          position: 'absolute',
          top: 380,
          left: 0,
          width: 1920,
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'center',
        }}
      >
        {/* Line 1: ∀ input ∈ String: */}
        <div
          style={{
            fontFamily: FONT_MONO,
            fontSize: PROOF_LINES[0].size,
            color: PROOF_LINES[0].color,
            minHeight: 32,
            display: 'flex',
            alignItems: 'center',
          }}
        >
          {PROOF_LINES[0].text.substring(0, line1Visible)}
          {line1Visible < line1Chars && line1Visible > 0 && (
            <span
              style={{
                display: 'inline-block',
                width: 10,
                height: 22,
                backgroundColor: COLOR_PURPLE,
                marginLeft: 1,
                opacity: frame % 16 < 8 ? 0.8 : 0,
              }}
            />
          )}
        </div>

        {/* Line 2: parse(input) ∈ {Valid(id), None} */}
        <div
          style={{
            fontFamily: FONT_MONO,
            fontSize: PROOF_LINES[1].size,
            color: PROOF_LINES[1].color,
            minHeight: 28,
            marginTop: 16,
            display: 'flex',
            alignItems: 'center',
          }}
        >
          {PROOF_LINES[1].text.substring(0, line2Visible)}
          {line2Visible < line2Chars && line2Visible > 0 && (
            <span
              style={{
                display: 'inline-block',
                width: 8,
                height: 18,
                backgroundColor: COLOR_BLUE,
                marginLeft: 1,
                opacity: frame % 16 < 8 ? 0.8 : 0,
              }}
            />
          )}
        </div>

        {/* Proof steps */}
        <div
          style={{
            marginTop: 30,
            display: 'flex',
            flexDirection: 'column',
            alignItems: 'center',
            gap: 6,
            opacity: stepsOpacity * 0.5,
          }}
        >
          {PROOF_STEPS.map((step, i) => (
            <span
              key={i}
              style={{
                fontFamily: FONT_MONO,
                fontSize: 14,
                color: TEXT_MUTED,
              }}
            >
              {step}
            </span>
          ))}
        </div>
      </div>

      {/* Green flash */}
      {flashOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            top: 520,
            left: 760,
            width: 400,
            height: 80,
            borderRadius: 12,
            backgroundColor: COLOR_PASS,
            opacity: flashOpacity,
            filter: 'blur(30px)',
          }}
        />
      )}

      {/* PROVEN ✓ stamp */}
      {stampOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            top: 530,
            left: 0,
            width: 1920,
            display: 'flex',
            justifyContent: 'center',
          }}
        >
          <div
            style={{
              fontFamily: FONT_SANS,
              fontSize: 36,
              fontWeight: 700,
              color: COLOR_PASS,
              border: `2px solid ${COLOR_PASS}`,
              borderRadius: 8,
              padding: '6px 24px',
              transform: `scale(${stampScale}) rotate(-5deg)`,
              opacity: stampOpacity,
              letterSpacing: 3,
            }}
          >
            PROVEN ✓
          </div>
        </div>
      )}

      {/* Annotation */}
      <div
        style={{
          position: 'absolute',
          top: 680,
          left: 0,
          width: 1920,
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'center',
          opacity: annotationOpacity,
        }}
      >
        <span
          style={{
            fontFamily: FONT_SANS,
            fontSize: 16,
            fontWeight: 700,
            color: TEXT_PRIMARY,
            opacity: 0.8,
          }}
        >
          Not sampling. Mathematical proof.
        </span>
        <span
          style={{
            fontFamily: FONT_SANS,
            fontSize: 13,
            color: COLOR_AMBER,
            opacity: 0.6,
            marginTop: 12,
          }}
        >
          The chip design analogy isn&apos;t a metaphor. It&apos;s the same technology.
        </span>
      </div>
    </div>
  );
};

export default ProofSection;
