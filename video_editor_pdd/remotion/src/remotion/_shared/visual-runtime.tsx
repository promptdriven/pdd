import React, { createContext, useContext, useMemo } from "react";
import { Internals, useCurrentFrame, useVideoConfig } from "remotion";

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
  const sequenceOffset =
    sequenceContext?.cumulatedFrom !== undefined
      ? sequenceContext.cumulatedFrom + sequenceContext.relativeFrom
      : 0;

  const scaledFrame =
    slotDurationInFrames <= 1 || targetDurationInFrames <= 1
      ? 0
      : Math.round(
          (localFrame / Math.max(1, slotDurationInFrames - 1)) *
            Math.max(0, targetDurationInFrames - 1)
        );

  const scaledTimelineContext = useMemo(() => {
    return {
      ...timelineContext,
      frame: {
        ...timelineContext.frame,
        [videoConfig.id]: sequenceOffset + scaledFrame,
      },
    };
  }, [scaledFrame, sequenceOffset, timelineContext, videoConfig.id]);

  const scaledSequenceContext = useMemo(() => {
    if (!sequenceContext) {
      return sequenceContext;
    }

    return {
      ...sequenceContext,
      durationInFrames: targetDurationInFrames,
    };
  }, [sequenceContext, targetDurationInFrames]);

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
