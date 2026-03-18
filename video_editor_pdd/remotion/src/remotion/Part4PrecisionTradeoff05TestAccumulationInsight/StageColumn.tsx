import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import PromptDocument from './PromptDocument';
import MoldCrossSection from './MoldCrossSection';
import { PROMPT_DOC_WIDTH, MOLD_WIDTH, MOLD_HEIGHT, type StageData } from './constants';

interface StageColumnProps {
  stage: StageData;
  centerX: number;
  animStartFrame: number;
  animDuration: number;
  isLast?: boolean;
}

/**
 * A single stage column showing header, prompt document, mold, and label.
 */
const StageColumn: React.FC<StageColumnProps> = ({
  stage,
  centerX,
  animStartFrame,
  animDuration,
  isLast = false,
}) => {
  const frame = useCurrentFrame();

  // Overall column fade-in
  const fadeIn = interpolate(
    frame,
    [animStartFrame, animStartFrame + 30],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Y-slide from below
  const slideY = interpolate(
    frame,
    [animStartFrame, animStartFrame + 30],
    [20, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Position calculations
  const headerY = 120;
  const promptY = 155;
  const moldY = promptY + stage.promptHeight + 25;
  const labelY = moldY + MOLD_HEIGHT + 15;

  return (
    <div
      style={{
        position: 'absolute',
        left: centerX - PROMPT_DOC_WIDTH / 2 - 60,
        top: 0,
        width: PROMPT_DOC_WIDTH + 120,
        height: 600,
        opacity: fadeIn,
        transform: `translateY(${slideY}px)`,
      }}
    >
      {/* Stage header */}
      <div
        style={{
          position: 'absolute',
          top: headerY,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 13,
          fontWeight: 600,
          color: stage.color,
          opacity: 0.5,
          letterSpacing: 2,
        }}
      >
        {stage.label}
      </div>

      {/* Prompt document */}
      <div
        style={{
          position: 'absolute',
          top: promptY,
          left: '50%',
          transform: 'translateX(-50%)',
        }}
      >
        <PromptDocument
          width={PROMPT_DOC_WIDTH}
          height={stage.promptHeight}
          lineCount={stage.promptLines}
          lineColor="#4A90D9"
          lineOpacity={0.4}
          animStartFrame={animStartFrame + 5}
          animDuration={animDuration - 5}
        />
      </div>

      {/* Mold cross-section */}
      <div
        style={{
          position: 'absolute',
          top: moldY,
          left: '50%',
          transform: 'translateX(-50%)',
        }}
      >
        <MoldCrossSection
          width={MOLD_WIDTH}
          height={MOLD_HEIGHT}
          wallCount={stage.wallCount}
          wallColor="#D9944A"
          wallStroke={stage.wallStroke}
          fillColor="#4A90D9"
          fillOpacity={stage.fillOpacity}
          animStartFrame={animStartFrame + 15}
          animDuration={Math.max(20, animDuration - 20)}
          glow={
            isLast
              ? { color: '#5AAA6E', blur: 12, opacity: 0.1 }
              : undefined
          }
        />
      </div>

      {/* Label */}
      <div
        style={{
          position: 'absolute',
          top: labelY,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          color: stage.color,
          opacity: 0.5 * interpolate(
            frame,
            [animStartFrame + animDuration - 15, animStartFrame + animDuration],
            [0, 1],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
          ),
        }}
      >
        {stage.description}
      </div>
    </div>
  );
};

export default StageColumn;
