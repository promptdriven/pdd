import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { BG_COLOR, TIMING } from './constants';
import { SpectrumBar } from './SpectrumBar';
import { RegionLabels } from './RegionLabels';
import { Slider } from './Slider';
import { Notches } from './Notches';
import { KeyQuestion } from './KeyQuestion';

export const defaultPart4PrecisionTradeoff08PromptCodeSpectrumProps = {};

/**
 * Section 4.8: Prompt-Code Spectrum — The Fluid Boundary
 *
 * A horizontal spectrum/gradient bar from "Pure natural language" (blue) to
 * "Pure code" (gray). A slider at 25% shows most work stays in prompt space.
 * Region labels, notch markers, and a three-line key question build up
 * across 360 frames (12s @ 30fps).
 */
export const Part4PrecisionTradeoff08PromptCodeSpectrum: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Title — visible from frame 0 for immediate content */}
      <div
        style={{
          position: 'absolute',
          top: 80,
          left: 0,
          width: 1920,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 28,
          fontWeight: 700,
          color: '#E2E8F0',
          opacity: 0.8,
          letterSpacing: '-0.02em',
        }}
      >
        The Prompt–Code Spectrum
      </div>

      {/* Spectrum bar + endpoint labels (frames 0-30 draw, labels fade in) */}
      <Sequence from={0} durationInFrames={TIMING.totalFrames}>
        <SpectrumBar />
      </Sequence>

      {/* Region labels above spectrum (frames 30+) */}
      <Sequence from={0} durationInFrames={TIMING.totalFrames}>
        <RegionLabels />
      </Sequence>

      {/* Slider / thumb indicator (frames 60+) */}
      <Sequence from={0} durationInFrames={TIMING.totalFrames}>
        <Slider />
      </Sequence>

      {/* Code-dip notches (frames 120+) */}
      <Sequence from={0} durationInFrames={TIMING.totalFrames}>
        <Notches />
      </Sequence>

      {/* Key question text (frames 150+) */}
      <Sequence from={0} durationInFrames={TIMING.totalFrames}>
        <KeyQuestion />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff08PromptCodeSpectrum;
