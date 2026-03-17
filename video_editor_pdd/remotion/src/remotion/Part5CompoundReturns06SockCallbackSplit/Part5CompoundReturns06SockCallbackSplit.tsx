import React from "react";
import { AbsoluteFill, staticFile } from "remotion";
import { useVisualMediaSrc } from "../_shared/visual-runtime";

import { SplitPanel } from "./SplitPanel";
import { SplitDivider } from "./SplitDivider";
import { RealizationFlash } from "./RealizationFlash";
import { PanelCaption } from "./PanelCaption";
import { CrossedOutIcon } from "./CrossedOutIcon";
import {
  BG_COLOR,
  LEFT_PANEL_W,
  RIGHT_PANEL_X,
  RIGHT_PANEL_W,
  LEFT_GRADE_COLOR,
  LEFT_GRADE_OPACITY,
  LEFT_HEADER_COLOR,
  LEFT_VIGNETTE_EDGE,
  RIGHT_GRADE_COLOR,
  RIGHT_GRADE_OPACITY,
  RIGHT_HEADER_COLOR,
  RIGHT_VIGNETTE_EDGE,
  LEFT_ICON_X,
  LEFT_ICON_Y,
  RIGHT_ICON_X,
  RIGHT_ICON_Y,
} from "./constants";

export const defaultPart5CompoundReturns06SockCallbackSplitProps = {};

export const Part5CompoundReturns06SockCallbackSplit: React.FC = () => {
  // Resolve media from wrapper aliases, with static fallbacks
  const leftSrc = useVisualMediaSrc(
    "leftSrc",
    staticFile("veo/grandmother_realization.mp4")
  );
  const rightSrc = useVisualMediaSrc(
    "rightSrc",
    staticFile("veo/developer_prompt_shift.mp4")
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* ── Left Panel: 1960s Grandmother ── */}
      <SplitPanel
        x={0}
        width={LEFT_PANEL_W}
        headerText="1960"
        headerColor={LEFT_HEADER_COLOR}
        gradeColor={LEFT_GRADE_COLOR}
        gradeOpacity={LEFT_GRADE_OPACITY}
        vignetteEdge={LEFT_VIGNETTE_EDGE}
        videoSrc={leftSrc}
      >
        <PanelCaption side="left" />
        <CrossedOutIcon
          variant="needle"
          color={LEFT_HEADER_COLOR}
          opacity={0.3}
          x={LEFT_ICON_X}
          y={LEFT_ICON_Y}
        />
      </SplitPanel>

      {/* ── Split Divider ── */}
      <SplitDivider />

      {/* ── Right Panel: Modern Developer ── */}
      <SplitPanel
        x={RIGHT_PANEL_X}
        width={RIGHT_PANEL_W}
        headerText="NOW"
        headerColor={RIGHT_HEADER_COLOR}
        gradeColor={RIGHT_GRADE_COLOR}
        gradeOpacity={RIGHT_GRADE_OPACITY}
        vignetteEdge={RIGHT_VIGNETTE_EDGE}
        videoSrc={rightSrc}
      >
        <PanelCaption side="right" />
        <CrossedOutIcon
          variant="patch"
          color={RIGHT_HEADER_COLOR}
          opacity={0.3}
          x={RIGHT_ICON_X}
          y={RIGHT_ICON_Y}
        />
      </SplitPanel>

      {/* ── Realization Flash (shared moment at frame 180) ── */}
      <RealizationFlash />
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns06SockCallbackSplit;
