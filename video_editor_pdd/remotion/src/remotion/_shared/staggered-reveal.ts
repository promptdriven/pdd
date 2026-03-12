export type BoundedStaggerOptions = {
  itemCount: number;
  startFrame: number;
  endFrame: number;
  desiredStepFrames: number;
  defaultFadeFrames: number;
  minFadeFrames?: number;
};

export type BoundedStaggerSchedule = {
  stepFrames: number;
  fadeFrames: number;
};

export const resolveBoundedStagger = ({
  itemCount,
  startFrame,
  endFrame,
  desiredStepFrames,
  defaultFadeFrames,
  minFadeFrames = 1,
}: BoundedStaggerOptions): BoundedStaggerSchedule => {
  if (itemCount <= 1) {
    return {
      stepFrames: 0,
      fadeFrames: Math.max(endFrame - startFrame, minFadeFrames),
    };
  }

  const availableFrames = Math.max(endFrame - startFrame, minFadeFrames);
  const desiredCompletionFrame =
    (itemCount - 1) * desiredStepFrames + defaultFadeFrames;

  if (desiredCompletionFrame <= availableFrames) {
    return {
      stepFrames: desiredStepFrames,
      fadeFrames: defaultFadeFrames,
    };
  }

  const boundedStepFrames = Math.max(
    0,
    (availableFrames - minFadeFrames) / (itemCount - 1)
  );
  const boundedFadeFrames = Math.max(
    minFadeFrames,
    availableFrames - boundedStepFrames * (itemCount - 1)
  );

  return {
    stepFrames: boundedStepFrames,
    fadeFrames: boundedFadeFrames,
  };
};
