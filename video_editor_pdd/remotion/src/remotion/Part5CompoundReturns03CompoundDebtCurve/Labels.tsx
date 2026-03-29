import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  AMBER_CURVE_COLOR,
  GREEN_LINE_COLOR,
  CALLOUT_TEXT_COLOR,
  AXIS_LABEL_COLOR,
  FORMULA_FADE_START,
  FORMULA_FADE_DURATION,
  FLAT_LABEL_START,
  FLAT_LABEL_FADE_DURATION,
  CISQ_START,
  CISQ_FADE_DURATION,
} from './constants';

/** Formula label above the amber curve */
export const FormulaLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [FORMULA_FADE_START, FORMULA_FADE_START + FORMULA_FADE_DURATION],
    [0, 0.8],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 1100,
        top: 200,
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: 18,
        fontWeight: 400,
        color: AMBER_CURVE_COLOR,
        opacity,
        whiteSpace: 'nowrap',
      }}
    >
      Debt × (1 + Rate)<sup>Time</sup>
    </div>
  );
};

/** Label for the flat green regeneration line */
export const FlatLineLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [FLAT_LABEL_START, FLAT_LABEL_START + FLAT_LABEL_FADE_DURATION],
    [0, 0.8],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 1100,
        top: 700,
        fontFamily: 'Inter, sans-serif',
        fontSize: 16,
        fontWeight: 400,
        color: GREEN_LINE_COLOR,
        opacity,
        whiteSpace: 'nowrap',
      }}
    >
      Regeneration cost (debt resets each cycle)
    </div>
  );
};

/** CISQ $1.52 trillion callout on the steep section */
export const CISQCallout: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [CISQ_START, CISQ_START + CISQ_FADE_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <div style={{ position: 'absolute', left: 750, top: 165, opacity }}>
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 22,
          fontWeight: 700,
          color: CALLOUT_TEXT_COLOR,
          whiteSpace: 'nowrap',
        }}
      >
        $1.52 trillion/year
      </div>
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 400,
          color: AXIS_LABEL_COLOR,
          opacity: 0.6,
          marginTop: 4,
        }}
      >
        — CISQ
      </div>
    </div>
  );
};
