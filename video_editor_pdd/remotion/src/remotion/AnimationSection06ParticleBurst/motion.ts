import { Easing, interpolate } from "remotion";
import { PARTICLES, TIMING } from "./constants";

export const resolveParticleOpacity = ({
  frame,
  currentDistance,
  maxDistance,
}: {
  frame: number;
  currentDistance: number;
  maxDistance: number;
}): number => {
  const fadeStartDistance = maxDistance * PARTICLES.fadeStartRatio;

  let travelOpacity = 1;
  if (currentDistance > fadeStartDistance) {
    const fadeProgress =
      (currentDistance - fadeStartDistance) /
      Math.max(1, maxDistance - fadeStartDistance);
    travelOpacity = interpolate(fadeProgress, [0, 1], [1, PARTICLES.tailStartOpacity], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    });
  }

  if (frame <= TIMING.particleMoveEnd) {
    return travelOpacity;
  }

  return interpolate(
    frame,
    [TIMING.particleMoveEnd, TIMING.totalEnd],
    [travelOpacity, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );
};
