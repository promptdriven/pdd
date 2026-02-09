import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { VerilogBlock } from "./VerilogBlock";
import { PromptDocument } from "./PromptDocument";
import { GateNetlist } from "./GateNetlist";
import { SynopsysCheckmark } from "./SynopsysCheckmark";
import { FlowArrow } from "./FlowArrow";
import { COLORS, BEATS, MoldToPromptPropsType } from "./constants";

/**
 * Main composition for "Verilog Morphs to Prompt" (Section 2.10).
 *
 * Implements the chip-design-to-software transformation with THREE parallel morphs:
 * 1. Verilog code (LEFT) → Prompt document (RIGHT)
 * 2. Gate-level netlist (LEFT) → Software code (RIGHT)
 * 3. Synopsys checkmark (LEFT) → Test suite (RIGHT)
 *
 * Animation sequence:
 * 1. Frame 0-90: Setup — Verilog code, gate netlist, Synopsys checkmark visible (LEFT side)
 * 2. Frame 90-240: Primary morph — THREE parallel transformations (LEFT → RIGHT)
 * 3. Frame 240-360: Labels — "PROMPT" title, code text, test checkmarks, glows appear
 * 4. Frame 360-480: Relationship — flow arrow from prompt to code
 * 5. Frame 480-600: Hold — prompt + tests glowing (blue/amber), code present (gray, no glow)
 */
export const MoldToPrompt: React.FC<MoldToPromptPropsType> = ({
  showNarration = true,
}) => {
  const frame = useCurrentFrame();

  // Narration fade-in at frame 360
  const narrationOpacity = showNarration
    ? interpolate(
        frame,
        [BEATS.NARRATION_START, BEATS.NARRATION_START + 40],
        [0, 1],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        }
      )
    : 0;

  // Chip design context labels (LEFT side, fades out as morph begins)
  const leftLabelsOpacity = interpolate(
    frame,
    [0, 20, BEATS.MORPH_START, BEATS.MORPH_START + 30],
    [0, 0.6, 0.6, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Software context labels (RIGHT side, fades in during labels phase)
  const rightLabelsOpacity = interpolate(
    frame,
    [BEATS.LABELS_START, BEATS.LABELS_START + 40],
    [0, 0.6],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {/* SVG canvas for all shapes */}
      <svg
        width="1920"
        height="1080"
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* MORPH 1: Verilog code → Prompt document */}
        <VerilogBlock />
        <PromptDocument />

        {/* MORPH 2: Gate netlist → Software code */}
        <GateNetlist />

        {/* MORPH 3: Synopsys checkmark → Test suite */}
        <SynopsysCheckmark />

        {/* Flow arrow from prompt to code */}
        <FlowArrow />
      </svg>

      {/* LEFT side context labels (chip design) */}
      {leftLabelsOpacity > 0 && (
        <>
          <div
            style={{
              position: "absolute",
              top: 140,
              left: 260,
              opacity: leftLabelsOpacity,
            }}
          >
            <div
              style={{
                fontSize: 12,
                fontFamily: "'JetBrains Mono', monospace",
                fontWeight: 500,
                textTransform: "uppercase" as const,
                letterSpacing: 2,
                color: "rgba(42, 161, 152, 0.6)",
              }}
            >
              Verilog Code
            </div>
          </div>

          <div
            style={{
              position: "absolute",
              top: 520,
              left: 280,
              opacity: leftLabelsOpacity,
            }}
          >
            <div
              style={{
                fontSize: 12,
                fontFamily: "'JetBrains Mono', monospace",
                fontWeight: 500,
                textTransform: "uppercase" as const,
                letterSpacing: 2,
                color: "rgba(26, 122, 110, 0.6)",
              }}
            >
              Gate-Level Netlist
            </div>
          </div>

          <div
            style={{
              position: "absolute",
              top: 730,
              left: 280,
              opacity: leftLabelsOpacity,
            }}
          >
            <div
              style={{
                fontSize: 12,
                fontFamily: "'JetBrains Mono', monospace",
                fontWeight: 500,
                textTransform: "uppercase" as const,
                letterSpacing: 2,
                color: "rgba(90, 170, 110, 0.6)",
              }}
            >
              Synopsys Verification
            </div>
          </div>
        </>
      )}

      {/* RIGHT side context labels (software) */}
      {rightLabelsOpacity > 0 && (
        <>
          <div
            style={{
              position: "absolute",
              top: 120,
              right: 340,
              opacity: rightLabelsOpacity,
            }}
          >
            <div
              style={{
                fontSize: 11,
                fontFamily: "'Inter', sans-serif",
                fontWeight: 500,
                textTransform: "uppercase" as const,
                letterSpacing: 2,
                color: "rgba(74, 144, 217, 0.5)",
              }}
            >
              Specification
            </div>
          </div>

          <div
            style={{
              position: "absolute",
              top: 580,
              right: 350,
              opacity: rightLabelsOpacity,
            }}
          >
            <div
              style={{
                fontSize: 11,
                fontFamily: "'Inter', sans-serif",
                fontWeight: 500,
                textTransform: "uppercase" as const,
                letterSpacing: 2,
                color: "rgba(160, 160, 160, 0.5)",
              }}
            >
              Generated Code
            </div>
          </div>

          <div
            style={{
              position: "absolute",
              top: 860,
              right: 350,
              opacity: rightLabelsOpacity,
            }}
          >
            <div
              style={{
                fontSize: 11,
                fontFamily: "'Inter', sans-serif",
                fontWeight: 500,
                textTransform: "uppercase" as const,
                letterSpacing: 2,
                color: "rgba(217, 148, 74, 0.5)",
              }}
            >
              Verification Tests
            </div>
          </div>
        </>
      )}

      {/* Narration overlay at frame 360 */}
      {narrationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 80,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: narrationOpacity,
          }}
        >
          <div
            style={{
              fontSize: 36,
              fontFamily: "'Inter', 'Helvetica Neue', Arial, sans-serif",
              fontWeight: 500,
              color: COLORS.NARRATION_WHITE,
              lineHeight: 1.5,
              maxWidth: 900,
              margin: "0 auto",
              letterSpacing: 0.5,
            }}
          >
            This is that same transition. For software.
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
