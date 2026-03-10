export type SlotScaledSequenceContext = {
  cumulatedFrom: number;
  relativeFrom: number;
  durationInFrames: number;
  parentFrom: number;
  id: string;
  height: number | null;
  width: number | null;
  premounting: boolean;
  postmounting: boolean;
  premountDisplay: number | null;
  postmountDisplay: number | null;
};

export const computeSlotScaledFrame = ({
  localFrame,
  slotDurationInFrames,
  intrinsicDurationInFrames,
}: {
  localFrame: number;
  slotDurationInFrames: number;
  intrinsicDurationInFrames: number;
}): number => {
  const safeSlotDuration = Math.max(1, Math.floor(slotDurationInFrames));
  const safeIntrinsicDuration = Math.max(1, Math.floor(intrinsicDurationInFrames));

  if (safeSlotDuration <= 1 || safeIntrinsicDuration <= 1) {
    return 0;
  }

  return Math.round(
    (localFrame / Math.max(1, safeSlotDuration - 1)) *
      Math.max(0, safeIntrinsicDuration - 1)
  );
};

export const buildSlotScaledSequenceContext = (
  sequenceContext: SlotScaledSequenceContext | null,
  intrinsicDurationInFrames: number
): SlotScaledSequenceContext | null => {
  if (!sequenceContext) {
    return sequenceContext;
  }

  return {
    ...sequenceContext,
    cumulatedFrom: 0,
    relativeFrom: 0,
    parentFrom: 0,
    durationInFrames: Math.max(1, Math.floor(intrinsicDurationInFrames)),
  };
};
