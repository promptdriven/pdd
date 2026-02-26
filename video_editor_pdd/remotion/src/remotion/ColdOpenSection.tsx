import React from "react";
import {
  AbsoluteFill,
  Audio,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Sequence,
} from "remotion";

import wordTimestamps from "./data/cold_open_words.json";

type WordEntry = { word: string; start: number; end: number; segmentId: string };

const Subtitles: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const currentTime = frame / fps;

  const words = wordTimestamps as WordEntry[];
  const visible = words.filter(
    (w) => currentTime >= w.start && currentTime <= w.end + 0.3
  );

  // Show a rolling window of recent words to prevent text from clipping frame edges
  const recentWords = visible.slice(-4);
  const text = recentWords.map((w) => w.word).join(" ");

  return (
    <div
      style={{
        position: "absolute",
        bottom: 80,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        padding: "0 10%",
        boxSizing: "border-box",
      }}
    >
      <div
        style={{
          backgroundColor: "rgba(0, 0, 0, 0.7)",
          color: "white",
          padding: "12px 24px",
          borderRadius: 8,
          fontSize: 28,
          fontFamily: "sans-serif",
          maxWidth: "80%",
          textAlign: "center",
          overflowWrap: "break-word",
          wordBreak: "break-word",
          overflow: "hidden",
          textOverflow: "ellipsis",
          boxSizing: "border-box",
        }}
      >
        {text}
      </div>
    </div>
  );
};

export const ColdOpenSection: React.FC = () => {
  const { durationInFrames, fps } = useVideoConfig();

  const opacity = interpolate(
    useCurrentFrame(),
    [0, 30, durationInFrames - 30, durationInFrames],
    [0, 1, 1, 0],
    { extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill style={{ opacity }}>
      <OffthreadVideo
        src={staticFile("veo/cold_open.mp4")}
        style={{ width: "100%", height: "100%" }}
      />
      <Audio src={staticFile("cold_open/narration.wav")} />
      <Subtitles />
    </AbsoluteFill>
  );
};

export default ColdOpenSection;
