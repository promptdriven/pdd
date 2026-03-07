import React from "react";
import {
  AbsoluteFill,
  Audio,
  Loop,
  OffthreadVideo,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";

import { BEATS, VISUAL_SEQUENCE, ColdOpenSectionPropsType } from "./constants";
import {
  ColdOpen01TitleCard,
  defaultColdOpen01TitleCardProps,
} from "../ColdOpen01TitleCard";
import {
  ColdOpen03SubtitleTrack,
  defaultColdOpen03SubtitleTrackProps,
} from "../03-SubtitleTrack";
import {
  ColdOpen05CrossfadeTransition,
  defaultColdOpen05CrossfadeTransitionProps,
} from "../ColdOpen05CrossfadeTransition";
import {
  ColdOpen06FadeBookends,
  defaultColdOpen06FadeBookendsProps,
} from "../06-FadeBookends";
import {
  ColdOpen07MonitorGlowOverlay,
  defaultColdOpen07MonitorGlowOverlayProps,
} from "../ColdOpen07MonitorGlowOverlay";
import {
  ColdOpen08ClosingQuestionCard,
  defaultColdOpen08ClosingQuestionCardProps,
} from "../08-ClosingQuestionCard";

export const ColdOpenSection: React.FC<ColdOpenSectionPropsType> = () => {
  const frame = useCurrentFrame();

  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      <Audio src={staticFile("cold_open_narration.wav")} />

      {/* Visual 0: 01_title_card */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <ColdOpen01TitleCard {...defaultColdOpen01TitleCardProps} />
        </Sequence>
      )}

      {/* Visual 1: 03_subtitle_track */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <ColdOpen03SubtitleTrack {...defaultColdOpen03SubtitleTrackProps} />
        </Sequence>
      )}

      {/* Visual 2: 05_crossfade_transition */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <ColdOpen05CrossfadeTransition
            {...defaultColdOpen05CrossfadeTransitionProps}
          />
        </Sequence>
      )}

      {/* Visual 3: 06_fade_bookends */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <ColdOpen06FadeBookends {...defaultColdOpen06FadeBookendsProps} />
        </Sequence>
      )}

      {/* Visual 4: 07_monitor_glow_overlay */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <ColdOpen07MonitorGlowOverlay
            {...defaultColdOpen07MonitorGlowOverlayProps}
          />
        </Sequence>
      )}

      {/* Visual 5: 08_closing_question_card */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <ColdOpen08ClosingQuestionCard
            {...defaultColdOpen08ClosingQuestionCardProps}
          />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
