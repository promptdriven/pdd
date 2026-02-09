import React from "react";
import {
  AbsoluteFill,
  Audio,
  Easing,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part5CompoundReturnsPropsType } from "./constants";
import { CompoundCurvesGraph } from "../46-CompoundCurvesGraph";
import { InvestmentTable } from "../47-InvestmentTable";
import { EconomicsChartReprise } from "../08-CrossingPoint";

/** Lower-third text overlay for callback video sections. */
const CallbackTextOverlay: React.FC<{
  frame: number;
  fadeStart: number;
  fadeEnd: number;
  children: React.ReactNode;
}> = ({ frame, fadeStart, fadeEnd, children }) => {
  const textOpacity = interpolate(
    frame,
    [fadeStart, fadeEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  return (
    <div
      style={{
        position: "absolute",
        bottom: 120,
        left: "50%",
        transform: "translateX(-50%)",
        backgroundColor: "rgba(26, 26, 46, 0.7)",
        padding: "12px 40px",
        borderRadius: 4,
        opacity: textOpacity,
      }}
    >
      {children}
    </div>
  );
};

export const Part5CompoundReturns: React.FC<Part5CompoundReturnsPropsType> = () => {
  const frame = useCurrentFrame();

  // Determine which visual is active based on frame position
  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  // Relative frame within the active visual's Sequence
  const localFrame5 = frame - BEATS.VISUAL_05_START;
  const localFrame6 = frame - BEATS.VISUAL_06_START;

  return (
    <AbsoluteFill style={{ backgroundColor: "#1a1a2e" }}>
      {/* Narration audio */}
      <Audio src={staticFile("part5_compound_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}

      {/* Visual 0: CompoundCurvesGraph phase 1 - Axes, legend, curve starts */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <CompoundCurvesGraph phase={1} />
        </Sequence>
      )}

      {/* Visual 1: CompoundCurvesGraph phase 2 - Patching curve draws, dots, annotations */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <CompoundCurvesGraph phase={2} />
        </Sequence>
      )}

      {/* Visual 2: CompoundCurvesGraph phase 3 - Wobbles, dips, $1.52T callout */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <CompoundCurvesGraph phase={3} />
        </Sequence>
      )}

      {/* Visual 3: CompoundCurvesGraph phases 4-5 - PDD curve, exponential, gap */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <CompoundCurvesGraph phase={5} />
        </Sequence>
      )}

      {/* Visual 4: InvestmentTable - Compound vs diminishing returns table */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <InvestmentTable showTable />
        </Sequence>
      )}

      {/* Visual 5: Grandmother callback with text overlay */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("07_split_screen_sepia.mp4")}
              style={{
                width: "100%",
                height: "100%",
                filter: "sepia(0.2) saturate(0.9)",
              }}
            />
            {/* Warm vignette overlay */}
            <div
              style={{
                position: "absolute",
                inset: 0,
                background:
                  "radial-gradient(ellipse at center, transparent 50%, rgba(26,26,46,0.4) 100%)",
              }}
            />
            {/* Text: "The economics made it rational." */}
            <CallbackTextOverlay
              frame={localFrame5}
              fadeStart={120}
              fadeEnd={150}
            >
              <span
                style={{
                  color: "white",
                  fontSize: 28,
                  fontFamily: "system-ui, sans-serif",
                  fontStyle: "italic",
                }}
              >
                The economics made it rational.
              </span>
            </CallbackTextOverlay>
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 6: Developer callback with text overlay */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("07_split_screen_sepia.mp4")}
              style={{
                width: "100%",
                height: "100%",
                filter: "saturate(0.9) brightness(0.95)",
              }}
            />
            {/* Cool vignette overlay */}
            <div
              style={{
                position: "absolute",
                inset: 0,
                background:
                  "radial-gradient(ellipse at center, transparent 50%, rgba(26,26,46,0.4) 100%)",
              }}
            />
            {/* Text: "Until now, the economics made it rational."
                Staggered fade: "Until now," fades in 20 frames before the rest
                to land the narrative pivot per spec lines 77-79, 98-106 */}
            {(() => {
              const untilNowOpacity = interpolate(
                localFrame6,
                [90, 120],
                [0, 1],
                {
                  extrapolateLeft: "clamp",
                  extrapolateRight: "clamp",
                  easing: Easing.out(Easing.cubic),
                },
              );
              const restOfTextOpacity = interpolate(
                localFrame6,
                [110, 140],
                [0, 1],
                {
                  extrapolateLeft: "clamp",
                  extrapolateRight: "clamp",
                  easing: Easing.out(Easing.cubic),
                },
              );
              return (
                <div
                  style={{
                    position: "absolute",
                    bottom: 120,
                    left: "50%",
                    transform: "translateX(-50%)",
                    backgroundColor: "rgba(26, 26, 46, 0.7)",
                    padding: "12px 40px",
                    borderRadius: 4,
                    opacity: Math.max(untilNowOpacity, restOfTextOpacity),
                  }}
                >
                  <span
                    style={{
                      color: "white",
                      fontSize: 28,
                      fontFamily: "system-ui, sans-serif",
                      fontStyle: "italic",
                    }}
                  >
                    <span
                      style={{
                        fontWeight: "bold",
                        opacity: untilNowOpacity,
                      }}
                    >
                      Until now,
                    </span>
                    <span style={{ opacity: restOfTextOpacity }}>
                      {" "}the economics made it rational.
                    </span>
                  </span>
                </div>
              );
            })()}
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 7: Economics Chart Reprise - "rational becomes... darning socks." */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START}>
          <EconomicsChartReprise />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
