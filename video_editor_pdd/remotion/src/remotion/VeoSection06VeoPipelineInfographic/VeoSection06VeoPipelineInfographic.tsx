import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  useVideoConfig,
} from 'remotion';
import {
  COLORS,
  ANIMATION,
  resolvePipelineInfographicLayout,
} from './constants';
import { PipelineNode } from './PipelineNode';
import { PipelineArrow } from './PipelineArrow';

export const VeoSection06VeoPipelineInfographic: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();
  const layout = resolvePipelineInfographicLayout(width, height);
  const { positions, typography } = layout;

  // Section title animation: fade in + slide down from top
  const titleOpacity = interpolate(
    frame,
    [ANIMATION.titleFadeStart, ANIMATION.titleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const titleY = interpolate(
    frame,
    [ANIMATION.titleFadeStart, ANIMATION.titleFadeEnd],
    [positions.titleY - 20, positions.titleY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Section title */}
      <div
        style={{
            position: 'absolute',
            top: titleY,
            left: 0,
            width,
            textAlign: 'center',
            fontFamily: typography.sectionTitle.fontFamily,
            fontSize: typography.sectionTitle.fontSize,
            fontWeight: typography.sectionTitle.fontWeight,
            color: COLORS.titleText,
            opacity: titleOpacity,
          }}
      >
        Veo Generation Pipeline
      </div>

      {/* Pipeline Node 1: Prompt */}
      <PipelineNode
        label="Prompt"
        icon="text-cursor"
        borderColor={COLORS.prompt}
        x={positions.node1X}
        nodeY={positions.nodeY}
        descriptorY={positions.descriptorY}
        scaleStart={ANIMATION.node1Start}
        scaleEnd={ANIMATION.node1End}
        descFadeStart={ANIMATION.desc1FadeStart}
        descFadeEnd={ANIMATION.desc1FadeEnd}
        descriptor="Text description"
        layout={layout}
      />

      {/* Arrow 1: Prompt → Veo 3.1 */}
      <PipelineArrow
        width={width}
        height={height}
        fromX={positions.arrow1Start}
        toX={positions.arrow1End}
        y={positions.arrowY}
        color={COLORS.prompt}
        drawStart={ANIMATION.arrow1Start}
        drawEnd={ANIMATION.arrow1End}
      />

      {/* Pipeline Node 2: Veo 3.1 */}
      <PipelineNode
        label="Veo 3.1"
        icon="sparkle"
        borderColor={COLORS.veo}
        x={positions.node2X}
        nodeY={positions.nodeY}
        descriptorY={positions.descriptorY}
        scaleStart={ANIMATION.node2Start}
        scaleEnd={ANIMATION.node2End}
        descFadeStart={ANIMATION.desc2FadeStart}
        descFadeEnd={ANIMATION.desc2FadeEnd}
        descriptor="AI video model"
        layout={layout}
      />

      {/* Arrow 2: Veo 3.1 → Clip */}
      <PipelineArrow
        width={width}
        height={height}
        fromX={positions.arrow2Start}
        toX={positions.arrow2End}
        y={positions.arrowY}
        color={COLORS.veo}
        drawStart={ANIMATION.arrow2Start}
        drawEnd={ANIMATION.arrow2End}
      />

      {/* Pipeline Node 3: Clip */}
      <PipelineNode
        label="Clip"
        icon="play-circle"
        borderColor={COLORS.clip}
        x={positions.node3X}
        nodeY={positions.nodeY}
        descriptorY={positions.descriptorY}
        scaleStart={ANIMATION.node3Start}
        scaleEnd={ANIMATION.node3End}
        descFadeStart={ANIMATION.desc3FadeStart}
        descFadeEnd={ANIMATION.desc3FadeEnd}
        descriptor="5s footage"
        layout={layout}
      />
    </AbsoluteFill>
  );
};

export const defaultVeoSection06VeoPipelineInfographicProps = {};

export default VeoSection06VeoPipelineInfographic;
