import React from "react";
import { AbsoluteFill, Sequence, useCurrentFrame } from "remotion";
import { DebtAreaChart } from "./DebtAreaChart";
import { PreviousAnnotations } from "./PreviousAnnotations";
import { AnnotationCallout } from "./AnnotationCallout";
import {
  BACKGROUND_COLOR,
  TOTAL_FRAMES,
  ANN1_APPEAR,
  ANN2_APPEAR,
  ANNOTATION1_X,
  ANNOTATION1_Y,
  ANNOTATION2_X,
  ANNOTATION2_Y,
} from "./constants";

export const defaultPart1Economics05CodeChurnAnnotationsProps = {};

/**
 * Section 1.5 — Code Churn & Refactoring Annotations (GitClear Data)
 *
 * Layers new annotation callouts onto the code-cost chart, highlighting
 * +44% code churn and −60% refactoring collapse from GitClear's 2025 study.
 *
 * 840 frames @ 30 fps ≈ 28 s
 */
export const Part1Economics05CodeChurnAnnotations: React.FC = () => {
  const frame = useCurrentFrame();

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        fontFamily: "Inter, sans-serif",
      }}
    >
      {/* ── Background chart (always visible) ──────────────────── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES} name="Chart">
        <DebtAreaChart />
      </Sequence>

      {/* ── Previous annotations fade to 30% ───────────────────── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES} name="PrevAnnotations">
        <PreviousAnnotations />
      </Sequence>

      {/* ── Annotation 1: Code churn +44% ──────────────────────── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES} name="Annotation1">
        <AnnotationCallout
          appearFrame={ANN1_APPEAR}
          borderColor="#EF4444"
          mainText="Code churn: +44%"
          sourceText="(GitClear, 2025, 211M lines analyzed)"
          posX={ANNOTATION1_X}
          posY={ANNOTATION1_Y}
          connectorTargetX={1050}
          connectorTargetY={400}
        />
      </Sequence>

      {/* ── Annotation 2: Refactoring −60% ─────────────────────── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES} name="Annotation2">
        <AnnotationCallout
          appearFrame={ANN2_APPEAR}
          borderColor="#F59E0B"
          mainText="Refactoring: −60%"
          sourceText="(GitClear, 2025, code revised within 2 weeks)"
          posX={ANNOTATION2_X}
          posY={ANNOTATION2_Y}
          connectorTargetX={1080}
          connectorTargetY={520}
        />
      </Sequence>

      {/* ── Bottom status bar for narration context ─────────────── */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES} name="StatusBar">
        <BottomBar frame={frame} />
      </Sequence>
    </AbsoluteFill>
  );
};

// ── Subtle bottom bar showing narration segment context ─────────
const BottomBar: React.FC<{ frame: number }> = ({ frame }) => {
  const seg = frame < 670 ? "part1_economics_012" : "part1_economics_013";
  const narrationSnippet =
    frame < 670
      ? "And GitClear confirmed it across 211 million lines of code..."
      : "But there's a second kind of debt hiding in there...";

  return (
    <div
      style={{
        position: "absolute",
        bottom: 0,
        left: 0,
        width: 1920,
        height: 48,
        background: "rgba(0,0,0,0.55)",
        display: "flex",
        alignItems: "center",
        paddingLeft: 32,
        paddingRight: 32,
      }}
    >
      {/* Segment ID chip */}
      <div
        style={{
          fontFamily: "Inter, monospace",
          fontSize: 11,
          fontWeight: 600,
          color: "#475569",
          background: "#1E293B",
          borderRadius: 4,
          padding: "3px 8px",
          marginRight: 14,
        }}
      >
        {seg}
      </div>

      {/* Divider */}
      <div
        style={{
          width: 2,
          height: 20,
          background: "#334155",
          opacity: 0.8,
          marginRight: 14,
        }}
      />

      {/* Narration preview */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 13,
          color: "#94A3B8",
          opacity: 0.78,
          whiteSpace: "nowrap",
          overflow: "hidden",
          textOverflow: "ellipsis",
          maxWidth: 1600,
        }}
      >
        {narrationSnippet}
      </div>
    </div>
  );
};

export default Part1Economics05CodeChurnAnnotations;
