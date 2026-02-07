import React from "react";
import {
  AbsoluteFill,
  Audio,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { VISUAL_SEQUENCE, ColdOpenSectionPropsType } from "./constants";


export const ColdOpenSection: React.FC<ColdOpenSectionPropsType> = () => {
  const frame = useCurrentFrame();

  // Determine which visual is active based on frame position
  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      {/* Narration audio */}
      <Audio src={staticFile("cold_open_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: Veo clip - If you use Cursor, Claude Code, Copilot, getting g */}
      {activeVisual === 0 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_split_screen_sepia.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 1: Veo clip - Great-grandmother figured out sixty years ago */}
      {activeVisual === 1 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_split_screen_sepia.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 2: Veo clip - When socks got cheap enough she stopped */}
      {activeVisual === 2 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_split_screen_sepia.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 3: Veo clip - Code just got that cheap */}
      {activeVisual === 3 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_split_screen_sepia.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 4: Veo clip - So why are we still patching */}
      {activeVisual === 4 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_split_screen_sepia.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}
    </AbsoluteFill>
  );
};
