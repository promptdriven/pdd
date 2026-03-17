import React, { useMemo } from "react";
import {
  CODE_FONT,
  CODE_FONT_SIZE,
  DIFF_ADDED_COLOR,
  DIFF_ADDED_BG_OPACITY,
  DIFF_DELETED_COLOR,
  DIFF_DELETED_BG_OPACITY,
  DIFF_UNCHANGED_COLOR,
  DIFF_UNCHANGED_OPACITY,
  DIFF_BG_COLOR,
  WIDTH,
  HEIGHT,
  seededRandom,
} from "./constants";

/**
 * A scrolling code diff display.
 * Generates realistic-looking diff lines and scrolls them upward.
 * scrollOffset controls the vertical pixel offset of the scroll.
 */

type DiffLineType = "added" | "deleted" | "unchanged";

interface DiffLine {
  type: DiffLineType;
  text: string;
  lineNumber: number;
}

// Code snippets for realistic-looking diff content
const CODE_FRAGMENTS = {
  added: [
    "  const result = await processChipLayout(gates);",
    "  if (verifyNetlist(output)) {",
    '    logger.info("Synthesis complete", { gateCount });',
    "  return optimizeRouting(netlist, constraints);",
    "  const placement = runPlacement(design);",
    '  export function validateTiming(clock: number): boolean {',
    "    yield* generateVerilog(module);",
    "  const drc = checkDesignRules(layout);",
    "    await synthesize(hdlSource, targetLib);",
    "  function routeSignal(src: Pin, dst: Pin) {",
    '    const buffer = insertBuffer(net, "high_drive");',
    "  if (slackNs < 0) fixTimingViolation(path);",
    "  const area = estimateArea(gateList);",
    "    power += leakagePower(cell) + switchingPower(cell, activity);",
    "  for (const net of criticalNets) {",
    "    const fanout = computeFanout(driver, loads);",
    '  assert(coverage > 0.95, "Insufficient coverage");',
    "  const floorplan = partitionDesign(modules);",
    "    registerMap.set(addr, defaultValue);",
    "  if (congestion > threshold) reroute(region);",
  ],
  deleted: [
    "  // TODO: manual review needed",
    "  const result = legacyProcess(input);",
    "  if (checkManually(output)) {",
    '    console.log("Check completed");',
    "  return oldRoutingAlgorithm(netlist);",
    "  const placement = manualPlacement(design);",
    "  // This function is deprecated",
    "    throw new Error('Review timeout');",
    "  const drc = manualDrcCheck(layout);",
    "    await legacySynthesize(source);",
    "  function routeByHand(src: Pin, dst: Pin) {",
    "  // FIXME: timing violation in critical path",
    "  const area = roughEstimate(gateList);",
    "    power += estimatedPower(cell);",
    "  for (const net of allNets) {",
    "    const fanout = approximateFanout(driver);",
  ],
  unchanged: [
    "import { ChipDesign } from './types';",
    "import { NetlistParser } from './parser';",
    "",
    "interface SynthesisConfig {",
    "  targetFrequency: number;",
    "  maxArea: number;",
    "  powerBudget: number;",
    "}",
    "",
    "export class DesignCompiler {",
    "  private netlist: Netlist;",
    "  private constraints: TimingConstraints;",
    "",
    "  constructor(config: SynthesisConfig) {",
    "    this.config = config;",
    "  }",
    "",
    "  async compile(): Promise<Layout> {",
    "    const parsed = this.parse();",
    "    return this.optimize(parsed);",
    "  }",
    "}",
  ],
};

function generateDiffLines(count: number): DiffLine[] {
  const rng = seededRandom(123);
  const lines: DiffLine[] = [];
  let lineNum = 1;

  for (let i = 0; i < count; i++) {
    const r = rng();
    let type: DiffLineType;
    if (r < 0.35) {
      type = "added";
    } else if (r < 0.55) {
      type = "deleted";
    } else {
      type = "unchanged";
    }

    const fragments = CODE_FRAGMENTS[type];
    const idx = Math.floor(rng() * fragments.length);
    const text = fragments[idx];

    lines.push({ type, text, lineNumber: lineNum });
    lineNum++;
  }

  return lines;
}

const LINE_HEIGHT = 18;
const PADDING_LEFT = 60;
const PADDING_TOP = 20;

export const ScrollingCodeDiff: React.FC<{
  scrollOffset: number;
  opacity: number;
}> = ({ scrollOffset, opacity }) => {
  // Generate enough lines to fill the scroll range
  // Max scroll: 30px/frame * 240 frames = 7200px, plus screen height
  const totalLines = 600;
  const lines = useMemo(() => generateDiffLines(totalLines), []);

  const totalHeight = totalLines * LINE_HEIGHT;

  // Calculate visible range
  const visibleTop = scrollOffset;
  const visibleBottom = scrollOffset + HEIGHT;
  const startIdx = Math.max(0, Math.floor(visibleTop / LINE_HEIGHT) - 1);
  const endIdx = Math.min(
    totalLines,
    Math.ceil(visibleBottom / LINE_HEIGHT) + 1
  );

  const visibleLines = lines.slice(startIdx, endIdx);

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: WIDTH,
        height: HEIGHT,
        overflow: "hidden",
        backgroundColor: DIFF_BG_COLOR,
        opacity,
      }}
    >
      <div
        style={{
          position: "absolute",
          top: -scrollOffset + PADDING_TOP,
          left: 0,
          width: WIDTH,
          height: totalHeight,
        }}
      >
        {visibleLines.map((line, i) => {
          const actualIdx = startIdx + i;
          const y = actualIdx * LINE_HEIGHT;
          const bgColor =
            line.type === "added"
              ? DIFF_ADDED_COLOR
              : line.type === "deleted"
                ? DIFF_DELETED_COLOR
                : "transparent";
          const bgOpacity =
            line.type === "added"
              ? DIFF_ADDED_BG_OPACITY
              : line.type === "deleted"
                ? DIFF_DELETED_BG_OPACITY
                : 0;
          const prefix =
            line.type === "added"
              ? "+"
              : line.type === "deleted"
                ? "-"
                : " ";
          const prefixColor =
            line.type === "added"
              ? DIFF_ADDED_COLOR
              : line.type === "deleted"
                ? DIFF_DELETED_COLOR
                : DIFF_UNCHANGED_COLOR;
          const textColor =
            line.type === "unchanged" ? DIFF_UNCHANGED_COLOR : "#E2E8F0";
          const textOpacity =
            line.type === "unchanged" ? DIFF_UNCHANGED_OPACITY : 0.8;

          return (
            <div
              key={actualIdx}
              style={{
                position: "absolute",
                top: y,
                left: 0,
                width: WIDTH,
                height: LINE_HEIGHT,
                display: "flex",
                alignItems: "center",
              }}
            >
              {/* Background highlight for added/deleted */}
              {bgOpacity > 0 && (
                <div
                  style={{
                    position: "absolute",
                    top: 0,
                    left: 0,
                    width: WIDTH,
                    height: LINE_HEIGHT,
                    backgroundColor: bgColor,
                    opacity: bgOpacity,
                  }}
                />
              )}
              {/* Line number */}
              <span
                style={{
                  fontFamily: CODE_FONT,
                  fontSize: CODE_FONT_SIZE,
                  color: DIFF_UNCHANGED_COLOR,
                  opacity: 0.2,
                  width: 50,
                  textAlign: "right",
                  paddingRight: 8,
                  userSelect: "none",
                  position: "relative",
                }}
              >
                {line.lineNumber}
              </span>
              {/* Prefix (+/-/space) */}
              <span
                style={{
                  fontFamily: CODE_FONT,
                  fontSize: CODE_FONT_SIZE,
                  color: prefixColor,
                  opacity: 0.7,
                  width: 16,
                  position: "relative",
                }}
              >
                {prefix}
              </span>
              {/* Code text */}
              <span
                style={{
                  fontFamily: CODE_FONT,
                  fontSize: CODE_FONT_SIZE,
                  color: textColor,
                  opacity: textOpacity,
                  paddingLeft: PADDING_LEFT - 66,
                  whiteSpace: "pre",
                  position: "relative",
                }}
              >
                {line.text}
              </span>
            </div>
          );
        })}
      </div>
    </div>
  );
};

export default ScrollingCodeDiff;
