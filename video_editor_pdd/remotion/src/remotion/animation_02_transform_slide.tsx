import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
  spring,
  useVideoConfig,
} from "remotion";

export const Animation02TransformSlide: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Duration is ~5 seconds = 150 frames at 30fps
  const totalFrames = fps * 5;

  // Morph: border-radius and fill color over first 1.5s (~45 frames)
  const morphProgress = spring({
    frame,
    fps,
    config: {
      damping: 15,
      stiffness: 80,
      mass: 0.8,
    },
    durationInFrames: Math.round(fps * 1.5),
  });

  // Border radius: 120px (circle) -> 8px (rounded square)
  const borderRadius = interpolate(morphProgress, [0, 1], [120, 8]);

  // Size: 240px (circle diameter) -> 200px (square side)
  const size = interpolate(morphProgress, [0, 1], [240, 200]);

  // Color interpolation from #3B82F6 (blue) to #22C55E (green)
  const r = Math.round(interpolate(morphProgress, [0, 1], [59, 34]));
  const g = Math.round(interpolate(morphProgress, [0, 1], [130, 197]));
  const b = Math.round(interpolate(morphProgress, [0, 1], [246, 94]));
  const fillColor = `rgb(${r}, ${g}, ${b})`;

  // Slide: translateX from 0 to 300px with ease-in-out over full duration
  const slideX = interpolate(frame, [0, totalFrames - 15], [0, 300], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.ease),
  });

  // Opacity: hold at 1.0, then fade out over final 15 frames
  const opacity = interpolate(
    frame,
    [totalFrames - 15, totalFrames],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: "#FF0000",
        justifyContent: "center",
        alignItems: "center",
      }}
    >
      <div
        style={{
          width: size,
          height: size,
          borderRadius,
          backgroundColor: fillColor,
          opacity,
          transform: `translateX(${slideX}px)`,
        }}
      />
    </AbsoluteFill>
  );
};

export default Animation02TransformSlide;
