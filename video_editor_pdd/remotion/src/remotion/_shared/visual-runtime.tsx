import React, { createContext, useContext, useMemo } from "react";
import { Internals, useCurrentFrame, useVideoConfig } from "remotion";
import {
  buildSlotScaledSequenceContext,
  computeSlotScaledFrame,
} from "./slot-scaled-runtime";

export type VisualMedia = {
  defaultSrc?: string;
  backgroundSrc?: string;
  outputSrc?: string;
  leftSrc?: string;
  rightSrc?: string;
  baseSrc?: string;
  revealSrc?: string;
};

const VisualMediaContext = createContext<VisualMedia | null>(null);

export const VisualMediaProvider: React.FC<{
  media?: VisualMedia | null;
  children: React.ReactNode;
}> = ({ media, children }) => {
  return (
    <VisualMediaContext.Provider value={media ?? null}>
      {children}
    </VisualMediaContext.Provider>
  );
};

export const useVisualMediaSrc = (
  key: keyof VisualMedia = "defaultSrc",
  fallback?: string
): string | null => {
  const media = useContext(VisualMediaContext);
  return media?.[key] ?? media?.defaultSrc ?? fallback ?? null;
};

export const SlotScaledSequence: React.FC<{
  intrinsicDurationInFrames: number;
  children: React.ReactNode;
}> = ({ intrinsicDurationInFrames, children }) => {
  const localFrame = useCurrentFrame();
  const videoConfig = useVideoConfig();
  const sequenceContext = useContext(Internals.SequenceContext);
  const timelineContext = useContext(Internals.TimelineContext);

  const slotDurationInFrames = Math.max(
    1,
    sequenceContext?.durationInFrames ?? videoConfig.durationInFrames
  );
  const targetDurationInFrames = Math.max(
    1,
    Math.floor(intrinsicDurationInFrames)
  );
  const scaledFrame = computeSlotScaledFrame({
    localFrame,
    slotDurationInFrames,
    intrinsicDurationInFrames: targetDurationInFrames,
  });
  const scaledSequenceContext = useMemo(() => {
    // Reset offsets to { cumulatedFrom: 0, relativeFrom: 0, parentFrom: 0 }
    // so nested visuals use the full intrinsic frame range for the active slot.
    return buildSlotScaledSequenceContext(
      sequenceContext,
      targetDurationInFrames
    );
  }, [sequenceContext, targetDurationInFrames]);
  const scaledSequenceOffset =
    scaledSequenceContext?.cumulatedFrom !== undefined
      ? scaledSequenceContext.cumulatedFrom +
        scaledSequenceContext.relativeFrom
      : 0;

  const scaledTimelineContext = useMemo(() => {
    return {
      ...timelineContext,
      frame: {
        ...timelineContext.frame,
        [videoConfig.id]: scaledSequenceOffset + scaledFrame,
      },
    };
  }, [scaledFrame, scaledSequenceOffset, timelineContext, videoConfig.id]);

  const content = scaledSequenceContext ? (
    <Internals.SequenceContext.Provider value={scaledSequenceContext}>
      {children}
    </Internals.SequenceContext.Provider>
  ) : (
    <>{children}</>
  );

  return (
    <Internals.TimelineContext.Provider value={scaledTimelineContext}>
      {content}
    </Internals.TimelineContext.Provider>
  );
};
