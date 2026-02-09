import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part2ParadigmShiftPropsType } from "./constants";
import { DefectDiscovered, defaultDefectDiscoveredProps } from "../15-DefectDiscovered";
import { EngineerFixesMold, defaultEngineerFixesMoldProps } from "../15a-EngineerFixesMold";
import { ChipDesignHistory, defaultChipDesignHistoryProps } from "../19a-ChipDesignHistory";
import { PartsEject, defaultPartsEjectProps } from "../14-PartsEject";
import { PerfectParts, defaultPerfectPartsProps } from "../16-PerfectParts";
import { PlasticRegenerates, defaultPlasticRegeneratesProps } from "../18-PlasticRegenerates";
import { PromptGeneratesCode, defaultPromptGeneratesCodeProps } from "../20-PromptGeneratesCode";
import { ValueAura, defaultValueAuraProps } from "../17-ValueAura";

export const Part2ParadigmShift: React.FC<Part2ParadigmShiftPropsType> = () => {
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
      <Audio src={staticFile("part2_paradigm_shift_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: Veo clip - Pattern across industries, deeper shift in how thi */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("01_factory_floor.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 1: Veo clip - Consider injection molding, crafted to designed mo */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("02_mold_closeup.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 2: PartsEject - Make mold once, unlimited parts, refine once all i */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START}>
          <PartsEject {...defaultPartsEjectProps} />
        </Sequence>
      )}

      {/* Visual 3: DefectDiscovered - When there's a defect, don't patch individual part */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START}>
          <DefectDiscovered {...defaultDefectDiscoveredProps} />
        </Sequence>
      )}

      {/* Visual 4: EngineerFixesMold - Fix the mold, fix applies to every future part */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START}>
          <EngineerFixesMold {...defaultEngineerFixesMoldProps} />
        </Sequence>
      )}

      {/* Visual 5: PerfectParts - Result of fixing the mold, perfect parts eject */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START}>
          <PerfectParts {...defaultPerfectPartsProps} />
        </Sequence>
      )}

      {/* Visual 6: ValueAura - Migration of where value lives */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START}>
          <ValueAura {...defaultValueAuraProps} />
        </Sequence>
      )}

      {/* Visual 7: PlasticRegenerates - Molding value in specification, disposable, regene */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START}>
          <PlasticRegenerates {...defaultPlasticRegeneratesProps} />
        </Sequence>
      )}

      {/* Visual 8: Veo clip + transistor counter overlay - Not just plastics, chip industry hit this exact wall */}
      {activeVisual === 8 && (
        <Sequence from={BEATS.VISUAL_08_START}>
          <AbsoluteFill>
            <OffthreadVideo
              loop
              src={staticFile("07_craftsman_vs_mold.mp4")}
              style={{ width: "100%", height: "100%" }}
            />
            {/* Transistor counter overlay (spec 09b) */}
            {(() => {
              const localFrame = frame - BEATS.VISUAL_08_START;
              const duration = BEATS.VISUAL_08_END - BEATS.VISUAL_08_START;
              const counterProgress = interpolate(
                localFrame,
                [0, duration * 0.9],
                [0, 1],
                {
                  extrapolateLeft: "clamp",
                  extrapolateRight: "clamp",
                  easing: Easing.bezier(0.25, 0.1, 0.25, 1),
                }
              );
              const count = Math.round(
                100 * Math.pow(500, counterProgress)
              );
              const counterOpacity = interpolate(
                localFrame,
                [10, 30],
                [0, 1],
                {
                  extrapolateLeft: "clamp",
                  extrapolateRight: "clamp",
                }
              );
              const isBlinking =
                localFrame > duration * 0.9 &&
                Math.sin(localFrame * 0.3) > 0;
              return (
                <div
                  style={{
                    position: "absolute",
                    top: 40,
                    right: 40,
                    padding: "12px 20px",
                    borderRadius: 8,
                    backgroundColor: "rgba(30, 30, 46, 0.75)",
                    fontFamily:
                      "'JetBrains Mono', 'Fira Code', monospace",
                    fontSize: 22,
                    color:
                      localFrame > duration * 0.9
                        ? "#D9944A"
                        : "#2AA198",
                    opacity: isBlinking
                      ? counterOpacity * 0.3
                      : counterOpacity,
                    border: "1px solid rgba(42, 161, 152, 0.3)",
                  }}
                >
                  ~{count.toLocaleString()} transistors
                </div>
              );
            })()}
          </AbsoluteFill>
        </Sequence>
      )}

      {/* Visual 9: ChipDesignHistory (phase: verilogSynthesis) - 1980s drew gates by hand, moved to Verilog in 1985 */}
      {activeVisual === 9 && (
        <Sequence from={BEATS.VISUAL_09_START}>
          <ChipDesignHistory {...defaultChipDesignHistoryProps} phase="verilogSynthesis" />
        </Sequence>
      )}

      {/* Visual 10: ChipDesignHistory (phase: threeNetlists) - Synthesis non-deterministic, different gates every time */}
      {activeVisual === 10 && (
        <Sequence from={BEATS.VISUAL_10_START}>
          <ChipDesignHistory {...defaultChipDesignHistoryProps} phase="threeNetlists" />
        </Sequence>
      )}

      {/* Visual 11: ChipDesignHistory (phase: verification) - Synopsys wrapped verification, SAT/SMT proof, same function */}
      {activeVisual === 11 && (
        <Sequence from={BEATS.VISUAL_11_START}>
          <ChipDesignHistory {...defaultChipDesignHistoryProps} phase="verification" />
        </Sequence>
      )}

      {/* Visual 12: ChipDesignHistory (phase: abstractionTimeline) - By 1990 schematic, mid-90s half switched, all use HDL now */}
      {activeVisual === 12 && (
        <Sequence from={BEATS.VISUAL_12_START}>
          <ChipDesignHistory {...defaultChipDesignHistoryProps} phase="abstractionTimeline" />
        </Sequence>
      )}

      {/* Visual 13: PromptGeneratesCode - Same transition for software, prompt is mold, test */}
      {activeVisual === 13 && (
        <Sequence from={BEATS.VISUAL_13_START}>
          <PromptGeneratesCode {...defaultPromptGeneratesCodeProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
