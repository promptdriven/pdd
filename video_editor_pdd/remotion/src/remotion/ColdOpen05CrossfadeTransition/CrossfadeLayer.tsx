import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";

interface CrossfadeLayerProps {
  src: string;
  startFrom: number;
  direction: "in" | "out";
  crossfadeStart: number;
  crossfadeEnd: number;
}

export const CrossfadeLayer: React.FC<CrossfadeLayerProps> = ({
  src,
  startFrom,
  direction,
  crossfadeStart,
  crossfadeEnd,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [crossfadeStart, crossfadeEnd],
    direction === "out" ? [1, 0] : [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ opacity }}>
      <OffthreadVideo
        src={staticFile(src)}
        startFrom={startFrom}
        style={{ width: "100%", height: "100%", objectFit: "cover" }}
      />
    </AbsoluteFill>
  );
};
