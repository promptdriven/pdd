import React from "react";
import {
  AbsoluteFill,
  interpolate,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, ColdOpenSectionPropsType } from "./constants";


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
        <Sequence from={BEATS.VISUAL_00_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("cold_open_01a_establish.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 1: Veo clip - Great-grandmother figured out sixty years ago */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("cold_open_01d_zoom_out.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 2: Veo clip - When socks got cheap enough she stopped */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("cold_open_01f_modern_sock_toss.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 3: Code regeneration - Code just got that cheap */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <AbsoluteFill style={{ backgroundColor: "#1a1a2e" }}>
            {/* Old patched code - dissolves away */}
            <div style={{
              position: "absolute",
              top: "50%",
              left: "50%",
              transform: "translate(-50%, -50%)",
              opacity: interpolate(frame - BEATS.VISUAL_03_START, [0, 10, 11, 25], [1, 1, 1, 0], { extrapolateRight: "clamp" }),
              filter: `blur(${interpolate(frame - BEATS.VISUAL_03_START, [10, 25], [0, 8], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })}px)`,
            }}>
              <div style={{ background: "#1E1E2E", padding: 24, borderRadius: 12, border: "1px solid #E74C3C", width: 700 }}>
                <pre style={{ fontSize: 14, fontFamily: "'JetBrains Mono', monospace", color: "#8a9caf", margin: 0, lineHeight: 1.6 }}>{`def process_data(input):\n    # TODO: fix edge case\n    data = input.strip()  # patched\n    if len(data) > MAX:\n        data = data[:MAX]  # hotfix #2847\n    return validate(data)  # patched`}</pre>
              </div>
            </div>
            {/* New clean code - fades in */}
            <div style={{
              position: "absolute",
              top: "50%",
              left: "50%",
              transform: "translate(-50%, -50%)",
              opacity: interpolate(frame - BEATS.VISUAL_03_START, [18, 30], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
            }}>
              <div style={{ background: "#1E1E2E", padding: 24, borderRadius: 12, border: "1px solid #4CAF50", boxShadow: `0 0 ${interpolate(frame - BEATS.VISUAL_03_START, [28, 38], [0, 20], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })}px #4CAF50`, width: 700 }}>
                <pre style={{ fontSize: 14, fontFamily: "'JetBrains Mono', monospace", color: "#8a9caf", margin: 0, lineHeight: 1.6 }}>{`def process_data(input):\n    cleaned = sanitize(input)\n    validated = enforce_constraints(cleaned)\n    return validated`}</pre>
              </div>
            </div>
            {/* Terminal indicator */}
            <div style={{
              position: "absolute",
              bottom: 60,
              right: 60,
              opacity: interpolate(frame - BEATS.VISUAL_03_START, [25, 35], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 18,
              color: "#4CAF50",
            }}>
              $ pdd generate
            </div>
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 4: Title over code - So why are we still patching */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <AbsoluteFill style={{ backgroundColor: "#1a1a2e" }}>
            {/* Dimmed regenerated code in background */}
            <div style={{
              position: "absolute",
              top: "50%",
              left: "50%",
              transform: "translate(-50%, -50%)",
              opacity: 0.25,
            }}>
              <div style={{ background: "#1E1E2E", padding: 24, borderRadius: 12, border: "1px solid #4CAF50", width: 700 }}>
                <pre style={{ fontSize: 14, fontFamily: "'JetBrains Mono', monospace", color: "#8a9caf", margin: 0, lineHeight: 1.6 }}>{`def process_data(input):\n    cleaned = sanitize(input)\n    validated = enforce_constraints(cleaned)\n    return validated`}</pre>
              </div>
            </div>
            {/* Title text fading in */}
            <div style={{
              position: "absolute",
              top: 0, left: 0, right: 0, bottom: 0,
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              opacity: interpolate(frame - BEATS.VISUAL_04_START, [0, 20], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
            }}>
              <h1 style={{
                fontFamily: "'SF Pro Display', 'Helvetica Neue', sans-serif",
                fontSize: 72,
                fontWeight: 700,
                color: "#ffffff",
                letterSpacing: -1,
                margin: 0,
                textShadow: "0 0 40px rgba(0,0,0,0.8)",
              }}>
                Prompt-Driven Development
              </h1>
            </div>
          </AbsoluteFill>
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
