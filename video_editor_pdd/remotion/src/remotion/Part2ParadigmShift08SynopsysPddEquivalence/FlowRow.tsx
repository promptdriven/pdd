import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { StageIcon } from './StageIcon';
import type { StageData } from './constants';
import { TIMING, ARROW_COLOR } from './constants';

interface FlowRowProps {
  stages: StageData[];
  y: number;
}

const FlowArrow: React.FC<{
  fromX: number;
  toX: number;
  y: number;
  progress: number;
}> = ({ fromX, toX, y, progress }) => {
  // Arrow sits between two stage centers, with some padding for icons
  const arrowStartX = fromX + 45;
  const arrowEndX = toX - 45;
  const arrowLength = arrowEndX - arrowStartX;
  const drawnLength = arrowLength * progress;

  if (drawnLength <= 0) return null;

  return (
    <svg
      style={{
        position: 'absolute',
        left: arrowStartX,
        top: y - 1,
        width: arrowLength,
        height: 10,
        overflow: 'visible',
      }}
    >
      <line
        x1={0}
        y1={5}
        x2={drawnLength}
        y2={5}
        stroke={ARROW_COLOR}
        strokeWidth={1}
        opacity={0.3}
      />
      {/* Arrowhead */}
      {progress > 0.8 && (
        <polygon
          points={`${drawnLength},5 ${drawnLength - 6},2 ${drawnLength - 6},8`}
          fill={ARROW_COLOR}
          opacity={0.3 * Math.min(1, (progress - 0.8) / 0.2)}
        />
      )}
    </svg>
  );
};

export const FlowRow: React.FC<FlowRowProps> = ({ stages, y }) => {
  // useCurrentFrame() is already relative to the parent <Sequence from={...}>
  const relFrame = useCurrentFrame();

  return (
    <>
      {stages.map((stage, i) => {
        // Each stage fades in staggered
        const stageStart = i * TIMING.STAGE_STAGGER;
        const stageOpacity = interpolate(
          relFrame,
          [stageStart, stageStart + TIMING.STAGE_FADE],
          [0, 1],
          {
            easing: Easing.out(Easing.quad),
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
          }
        );

        // Arrow draws after stage appears
        const arrowStart = stageStart + TIMING.STAGE_FADE;
        const arrowProgress = i < stages.length - 1
          ? interpolate(
              relFrame,
              [arrowStart, arrowStart + TIMING.ARROW_DRAW],
              [0, 1],
              {
                easing: Easing.inOut(Easing.cubic),
                extrapolateLeft: 'clamp',
                extrapolateRight: 'clamp',
              }
            )
          : 0;

        return (
          <React.Fragment key={i}>
            {/* Stage icon + label */}
            <div
              style={{
                position: 'absolute',
                left: stage.x,
                top: y,
                opacity: stageOpacity,
                display: 'flex',
                flexDirection: 'column',
                alignItems: 'center',
              }}
            >
              <StageIcon
                icon={stage.icon}
                color={stage.color}
                opacity={0.5}
              />
              <div
                style={{
                  fontFamily: 'Inter, sans-serif',
                  fontSize: 11,
                  color: stage.color,
                  opacity: 0.5,
                  marginTop: 8,
                  whiteSpace: 'nowrap',
                  textAlign: 'center',
                  position: 'absolute',
                  top: 50,
                }}
              >
                {stage.name}
              </div>
            </div>

            {/* Arrow to next stage */}
            {i < stages.length - 1 && (
              <FlowArrow
                fromX={stage.x}
                toX={stages[i + 1].x}
                y={y}
                progress={arrowProgress}
              />
            )}
          </React.Fragment>
        );
      })}
    </>
  );
};

export default FlowRow;
