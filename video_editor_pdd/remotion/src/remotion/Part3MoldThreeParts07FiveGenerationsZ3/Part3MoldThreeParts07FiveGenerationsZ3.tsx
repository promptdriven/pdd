import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  Easing,
  interpolate,
} from 'remotion';
import {
  BG_COLOR,
  DURATION_FRAMES,
  PANEL_X_STARTS,
  PANEL_Y,
  CODE_VARIANTS,
  TEST_RESULTS,
  FONT_SANS,
  TEXT_PRIMARY,
  TEXT_SECONDARY,
  BEAT1_END,
  BEAT2_START,
  DISSOLVE_END,
  CAPTION_START,
} from './constants';
import { DotGrid } from './DotGrid';
import { CodePanel } from './CodePanel';
import { ProofSection } from './ProofSection';

export const defaultPart3MoldThreeParts07FiveGenerationsZ3Props = {};

export const Part3MoldThreeParts07FiveGenerationsZ3: React.FC = () => {
  const frame = useCurrentFrame();

  // Beat 1 fade-out / Beat 2 fade-in cross-dissolve (frames 300-330)
  const beat1Opacity = interpolate(
    frame,
    [BEAT2_START, DISSOLVE_END],
    [1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
  );

  const beat2Opacity = interpolate(
    frame,
    [BEAT2_START, DISSOLVE_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
  );

  // Caption fade-in (frames 240-260)
  const captionOpacity = interpolate(
    frame,
    [CAPTION_START, CAPTION_START + 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <DotGrid />

      {/* Beat 1: Five Generations */}
      {frame < DISSOLVE_END && (
        <AbsoluteFill style={{ opacity: beat1Opacity }}>
          {/* Five code panels */}
          {PANEL_X_STARTS.map((x, i) => (
            <CodePanel
              key={i}
              x={x}
              y={PANEL_Y}
              panelIndex={i}
              filename={`user_parser_v${i + 1}.py`}
              codeLines={CODE_VARIANTS[i]}
              testResult={TEST_RESULTS[i]}
              staggerDelay={i * 5}
            />
          ))}

          {/* Caption */}
          {frame >= CAPTION_START && (
            <div
              style={{
                position: 'absolute',
                top: 740,
                left: 0,
                width: 1920,
                display: 'flex',
                flexDirection: 'column',
                alignItems: 'center',
                opacity: captionOpacity,
              }}
            >
              <span
                style={{
                  fontFamily: FONT_SANS,
                  fontSize: 16,
                  color: TEXT_PRIMARY,
                  opacity: 0.7,
                }}
              >
                Generate five. Pick the one that passes all tests.
              </span>
              <span
                style={{
                  fontFamily: FONT_SANS,
                  fontSize: 13,
                  color: TEXT_SECONDARY,
                  opacity: 0.5,
                  marginTop: 12,
                }}
              >
                The walls don&apos;t care how many attempts it took.
              </span>
            </div>
          )}
        </AbsoluteFill>
      )}

      {/* Beat 2: Z3 Formal Proof */}
      {frame >= BEAT2_START && (
        <AbsoluteFill style={{ opacity: beat2Opacity }}>
          <Sequence from={BEAT2_START} durationInFrames={DURATION_FRAMES - BEAT2_START}>
            <ProofSection />
          </Sequence>
        </AbsoluteFill>
      )}
    </AbsoluteFill>
  );
};

export default Part3MoldThreeParts07FiveGenerationsZ3;
