import React, { createContext, useContext, useMemo } from "react";
import { Internals, staticFile, useCurrentFrame, useVideoConfig } from "remotion";
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
  leftBaseSrc?: string;
  leftRevealSrc?: string;
  rightBaseSrc?: string;
  rightRevealSrc?: string;
  baseSrc?: string;
  revealSrc?: string;
};

export type VisualContract = {
  specBaseName?: string;
  dataPoints?: Record<string, unknown> | null;
  mediaAliases?: VisualMedia | null;
  overlayConfig?: Record<string, unknown> | null;
  renderMode?: "raw-media" | "generated-media" | "component";
};

const VisualMediaContext = createContext<VisualMedia | null>(null);
const VisualContractContext = createContext<VisualContract | null>(null);

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

export const VisualContractProvider: React.FC<{
  contract?: VisualContract | null;
  children: React.ReactNode;
}> = ({ contract, children }) => {
  return (
    <VisualContractContext.Provider value={contract ?? null}>
      {children}
    </VisualContractContext.Provider>
  );
};

const SPLIT_ONLY_KEYS: ReadonlySet<keyof VisualMedia> = new Set([
  "leftSrc",
  "rightSrc",
  "leftBaseSrc",
  "leftRevealSrc",
  "rightBaseSrc",
  "rightRevealSrc",
]);

export const useVisualMediaSrc = (
  key: keyof VisualMedia = "defaultSrc",
  fallback?: string
): string | null => {
  const media = useContext(VisualMediaContext);
  const contract = useContext(VisualContractContext);
  const contractMedia =
    contract?.mediaAliases && typeof contract.mediaAliases === "object"
      ? contract.mediaAliases
      : null;
  if (SPLIT_ONLY_KEYS.has(key)) {
    return media?.[key] ?? contractMedia?.[key] ?? fallback ?? null;
  }
  return (
    media?.[key] ??
    media?.defaultSrc ??
    contractMedia?.[key] ??
    contractMedia?.defaultSrc ??
    fallback ??
    null
  );
};

export const useVisualMediaAssetSrc = (
  key: keyof VisualMedia = "defaultSrc",
  fallback?: string
): string | null => {
  const src = useVisualMediaSrc(key, fallback);
  if (!src) {
    return null;
  }

  if (
    src.startsWith("/") ||
    src.startsWith("http://") ||
    src.startsWith("https://") ||
    src.startsWith("data:") ||
    src.startsWith("blob:")
  ) {
    return src;
  }

  return staticFile(src);
};

export const useVisualContractData = <
  T extends Record<string, unknown> = Record<string, unknown>
>(): T | null => {
  const contract = useContext(VisualContractContext);
  const dataPoints = contract?.dataPoints;
  if (!dataPoints || typeof dataPoints !== "object" || Array.isArray(dataPoints)) {
    return null;
  }
  return dataPoints as T;
};

export const useVisualDurationInFrames = (): number => {
  const videoConfig = useVideoConfig();
  const sequenceContext = useContext(Internals.SequenceContext);

  return Math.max(
    1,
    Math.floor(sequenceContext?.durationInFrames ?? videoConfig.durationInFrames)
  );
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
