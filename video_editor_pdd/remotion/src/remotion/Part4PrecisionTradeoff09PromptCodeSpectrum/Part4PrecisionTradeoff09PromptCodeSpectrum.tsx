import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  BACKGROUND_COLOR,
  LABEL_FONT_FAMILY,
  BOTTOM_FONT_SIZE,
  PRIMARY_TEXT_COLOR,
  SECONDARY_TEXT_COLOR,
  NOTCHES,
  NOTCH_START,
  NOTCH_STAGGER,
  BOTTOM_PRIMARY_START,
  BOTTOM_SECONDARY_START,
  BOTTOM_FADE_DURATION,
  FADE_OUT_START,
  FADE_OUT_DURATION,
  TOTAL_FRAMES,
} from './constants';
import { SpectrumBar } from './SpectrumBar';
import { SliderThumb } from './SliderThumb';
import { NotchMark } from './NotchMark';

export const defaultPart4PrecisionTradeoff09PromptCodeSpectrumProps = {};

export const Part4PrecisionTradeoff09PromptCodeSpectrum: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Bottom primary text fade ──
  const primaryTextOpacity = interpolate(
    frame,
    [BOTTOM_PRIMARY_START, BOTTOM_PRIMARY_START + BOTTOM_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // ── Bottom secondary text fade ──
  const secondaryTextOpacity = interpolate(
    frame,
    [BOTTOM_SECONDARY_START, BOTTOM_SECONDARY_START + BOTTOM_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // ── Global fade-out ──
  const fadeOutOpacity = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
    [1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.quad) }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        opacity: fadeOutOpacity,
      }}
    >
      {/* Spectrum bar with gradient and zone fill */}
      <SpectrumBar />

      {/* Slider thumb */}
      <SliderThumb />

      {/* Notch marks — staggered pop-in */}
      {NOTCHES.map((notch, i) => (
        <NotchMark
          key={notch.label}
          fraction={notch.fraction}
          label={notch.label}
          appearFrame={NOTCH_START + i * NOTCH_STAGGER}
        />
      ))}

      {/* Bottom primary label */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          right: 0,
          top: 600,
          textAlign: 'center',
          fontFamily: LABEL_FONT_FAMILY,
          fontSize: BOTTOM_FONT_SIZE,
          fontWeight: 400,
          color: PRIMARY_TEXT_COLOR,
          opacity: primaryTextOpacity,
        }}
      >
        Stay in prompt space as long as possible.
      </div>

      {/* Bottom secondary label */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          right: 0,
          top: 640,
          textAlign: 'center',
          fontFamily: LABEL_FONT_FAMILY,
          fontSize: BOTTOM_FONT_SIZE,
          fontWeight: 400,
          color: SECONDARY_TEXT_COLOR,
          opacity: secondaryTextOpacity,
        }}
      >
        Dip into code when you must.
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff09PromptCodeSpectrum;
