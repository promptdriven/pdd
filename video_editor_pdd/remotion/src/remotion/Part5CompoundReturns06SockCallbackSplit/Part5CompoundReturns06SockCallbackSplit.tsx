import React from 'react';
import { AbsoluteFill } from 'remotion';
import { useVisualMediaAssetSrc } from '../_shared/visual-runtime';
import {
  WIDTH,
  HEIGHT,
  BG_COLOR,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_WIDTH,
  RIGHT_PANEL_X,
  LEFT_ACCENT,
  LEFT_GRADE_COLOR,
  LEFT_GRADE_OPACITY,
  LEFT_VIGNETTE_EDGE,
  RIGHT_ACCENT,
  RIGHT_GRADE_COLOR,
  RIGHT_GRADE_OPACITY,
  RIGHT_VIGNETTE_EDGE,
  CAPTION_COLOR,
  CAPTION_OPACITY,
  CAPTION_FONT_SIZE,
} from './constants';
import { SplitDivider } from './SplitDivider';
import { PanelContent } from './PanelContent';
import { CrossedOutIcon } from './CrossedOutIcon';

export const defaultPart5CompoundReturns06SockCallbackSplitProps = {};

export const Part5CompoundReturns06SockCallbackSplit: React.FC = () => {
  // Resolve Veo media sources via the visual-runtime hook.
  // For a split screen, we use leftSrc / rightSrc aliases.
  const leftVideoSrc = useVisualMediaAssetSrc('leftSrc');
  const rightVideoSrc = useVisualMediaAssetSrc('rightSrc');

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* ── Left Panel — 1960s Grandmother ── */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: LEFT_PANEL_WIDTH,
          height: HEIGHT,
        }}
      >
        <PanelContent
          side="left"
          panelWidth={LEFT_PANEL_WIDTH}
          headerText="1960"
          headerColor={LEFT_ACCENT}
          gradeColor={LEFT_GRADE_COLOR}
          gradeOpacity={LEFT_GRADE_OPACITY}
          vignetteEdge={LEFT_VIGNETTE_EDGE}
          videoSrc={leftVideoSrc}
          captionNode={
            <span
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: CAPTION_FONT_SIZE,
                fontStyle: 'italic',
                color: CAPTION_COLOR,
                opacity: CAPTION_OPACITY,
              }}
            >
              The economics made it rational.
            </span>
          }
          iconNode={
            <CrossedOutIcon
              type="needle"
              color={LEFT_ACCENT}
              opacity={0.3}
              x={200}
              y={900}
            />
          }
        />
      </div>

      {/* ── Split Divider ── */}
      <SplitDivider />

      {/* ── Right Panel — Modern Developer ── */}
      <div
        style={{
          position: 'absolute',
          left: RIGHT_PANEL_X,
          top: 0,
          width: RIGHT_PANEL_WIDTH,
          height: HEIGHT,
        }}
      >
        <PanelContent
          side="right"
          panelWidth={RIGHT_PANEL_WIDTH}
          headerText="NOW"
          headerColor={RIGHT_ACCENT}
          gradeColor={RIGHT_GRADE_COLOR}
          gradeOpacity={RIGHT_GRADE_OPACITY}
          vignetteEdge={RIGHT_VIGNETTE_EDGE}
          videoSrc={rightVideoSrc}
          captionNode={
            <span
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: CAPTION_FONT_SIZE,
                fontStyle: 'italic',
                color: CAPTION_COLOR,
              }}
            >
              <span style={{ opacity: CAPTION_OPACITY }}>Until now, </span>
              <span style={{ color: RIGHT_ACCENT, opacity: 0.8 }}>
                the economics made it rational.
              </span>
            </span>
          }
          iconNode={
            <CrossedOutIcon
              type="patch"
              color={RIGHT_ACCENT}
              opacity={0.3}
              x={718}
              y={900}
            />
          }
        />
      </div>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns06SockCallbackSplit;
