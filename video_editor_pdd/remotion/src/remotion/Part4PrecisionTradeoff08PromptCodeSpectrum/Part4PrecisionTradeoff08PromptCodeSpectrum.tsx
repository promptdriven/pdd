import React from 'react';
import { AbsoluteFill } from 'remotion';
import { BG_COLOR } from './constants';
import { SpectrumBar } from './SpectrumBar';
import { RegionLabels } from './RegionLabels';
import { SpectrumSlider } from './SpectrumSlider';
import { KeyQuestion } from './KeyQuestion';

export const defaultPart4PrecisionTradeoff08PromptCodeSpectrumProps = {};

/**
 * Section 4.8: Prompt-Code Spectrum — The Fluid Boundary
 *
 * A horizontal spectrum visualization showing the continuum from
 * natural language to code, with a slider indicating most specification
 * work stays on the natural-language side.
 *
 * Duration: 360 frames (12s @ 30fps)
 */
export const Part4PrecisionTradeoff08PromptCodeSpectrum: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Spectrum gradient bar with endpoint labels */}
      <SpectrumBar />

      {/* Region labels above the bar with connectors */}
      <RegionLabels />

      {/* Slider/thumb + code-dip notches */}
      <SpectrumSlider />

      {/* Key question text below the spectrum */}
      <KeyQuestion />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff08PromptCodeSpectrum;
