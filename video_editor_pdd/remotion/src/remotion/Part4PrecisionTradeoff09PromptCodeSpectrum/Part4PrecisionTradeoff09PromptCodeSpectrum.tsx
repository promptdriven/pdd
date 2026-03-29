import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  BACKGROUND_COLOR,
  FONT_FAMILY,
  PRIMARY_TEXT_COLOR,
  SECONDARY_TEXT_COLOR,
  NOTCH_DATA,
  PHASE_NOTCH_START,
  PHASE_NOTCH_STAGGER,
  PHASE_BOTTOM_LINE1_START,
  PHASE_BOTTOM_LINE2_START,
  PHASE_BOTTOM_FADE_DURATION,
  PHASE_FADEOUT_START,
  PHASE_FADEOUT_DURATION,
} from './constants';
import { SpectrumBar } from './SpectrumBar';
import { SliderThumb } from './SliderThumb';
import { NotchMark } from './NotchMark';

export const defaultPart4PrecisionTradeoff09PromptCodeSpectrumProps = {};

export const Part4PrecisionTradeoff09PromptCodeSpectrum: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Bottom label line 1 ──
  const line1Opacity = interpolate(
    frame,
    [PHASE_BOTTOM_LINE1_START, PHASE_BOTTOM_LINE1_START + PHASE_BOTTOM_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // ── Bottom label line 2 ──
  const line2Opacity = interpolate(
    frame,
    [PHASE_BOTTOM_LINE2_START, PHASE_BOTTOM_LINE2_START + PHASE_BOTTOM_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // ── Final fade to black ──
  const fadeOutOpacity = interpolate(
    frame,
    [PHASE_FADEOUT_START, PHASE_FADEOUT_START + PHASE_FADEOUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#000000' }}>
      <AbsoluteFill style={{ backgroundColor: BACKGROUND_COLOR, opacity: fadeOutOpacity }}>
        {/* Spectrum bar with endpoint labels */}
        <SpectrumBar />

        {/* Slider thumb + zone fill */}
        <SliderThumb />

        {/* Notch marks */}
        {NOTCH_DATA.map((notch, i) => (
          <NotchMark
            key={notch.label}
            fraction={notch.fraction}
            label={notch.label}
            appearFrame={PHASE_NOTCH_START + i * PHASE_NOTCH_STAGGER}
          />
        ))}

        {/* Bottom label — line 1 */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            right: 0,
            top: 600,
            textAlign: 'center',
            fontFamily: FONT_FAMILY,
            fontSize: 22,
            fontWeight: 400,
            color: PRIMARY_TEXT_COLOR,
            opacity: line1Opacity,
          }}
        >
          Stay in prompt space as long as possible.
        </div>

        {/* Bottom label — line 2 */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            right: 0,
            top: 640,
            textAlign: 'center',
            fontFamily: FONT_FAMILY,
            fontSize: 22,
            fontWeight: 400,
            color: SECONDARY_TEXT_COLOR,
            opacity: line2Opacity,
          }}
        >
          Dip into code when you must.
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff09PromptCodeSpectrum;
