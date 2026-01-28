import React, { useMemo } from "react";
import { Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { BEATS, COLORS } from "./constants";

interface CodeBlock {
  id: number;
  isRelevant: boolean;
  row: number;
  col: number;
}

export const SplitViewMismatch: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  // Fade in from context window view
  const fadeInOpacity = interpolate(
    frame,
    [BEATS.SPLIT_VIEW_START, BEATS.SPLIT_VIEW_START + 60],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Fade out to return to chart
  const fadeOutOpacity = interpolate(
    frame,
    [BEATS.SPLIT_VIEW_END - 60, BEATS.SPLIT_VIEW_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const opacity = Math.min(fadeInOpacity, fadeOutOpacity);

  // Panel dimensions
  const panelWidth = (width - 60) / 2 - 20; // Two panels with gap
  const panelHeight = height - 240;
  const panelTop = 140;

  // Grid configuration for the small "context window" grids
  const gridSize = 4; // 4x4 for visibility
  const blockGap = 8;
  const availableSize = Math.min(panelWidth - 80, panelHeight - 120);
  const blockSize = (availableSize - (gridSize - 1) * blockGap) / gridSize;

  // Generate "What AI sees" - mixed relevant/irrelevant
  const aiSeesBlocks = useMemo<CodeBlock[]>(() => {
    const blocks: CodeBlock[] = [];
    for (let row = 0; row < gridSize; row++) {
      for (let col = 0; col < gridSize; col++) {
        // Only ~30% is actually relevant
        const seed = row * gridSize + col;
        const isRelevant = seed % 10 < 3; // 30% relevant
        blocks.push({ id: seed, isRelevant, row, col });
      }
    }
    return blocks;
  }, [gridSize]);

  // Generate "What's actually needed" - all relevant
  const neededBlocks = useMemo<CodeBlock[]>(() => {
    const blocks: CodeBlock[] = [];
    for (let row = 0; row < gridSize; row++) {
      for (let col = 0; col < gridSize; col++) {
        blocks.push({ id: row * gridSize + col, isRelevant: true, row, col });
      }
    }
    return blocks;
  }, [gridSize]);

  // Animation: blocks slide in from sides
  const slideProgress = interpolate(
    frame,
    [BEATS.SPLIT_VIEW_START, BEATS.SPLIT_VIEW_START + 45],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.back(1.2)) }
  );

  const leftPanelX = interpolate(slideProgress, [0, 1], [-200, 30]);
  const rightPanelX = interpolate(slideProgress, [0, 1], [width, width / 2 + 10]);

  // Mismatch highlight animation
  const mismatchPulse = Math.sin(frame * 0.08) * 0.3 + 0.7;

  const renderGrid = (blocks: CodeBlock[], offsetX: number, offsetY: number) => {
    return blocks.map((block) => {
      const x = offsetX + block.col * (blockSize + blockGap);
      const y = offsetY + block.row * (blockSize + blockGap);

      return (
        <g key={block.id}>
          <rect
            x={x}
            y={y}
            width={blockSize}
            height={blockSize}
            rx={6}
            fill={block.isRelevant ? COLORS.RELEVANT_CODE : COLORS.IRRELEVANT_CODE}
            opacity={block.isRelevant ? 0.9 : 0.6 * mismatchPulse}
          />
          {/* Code lines inside blocks */}
          <rect
            x={x + blockSize * 0.15}
            y={y + blockSize * 0.2}
            width={blockSize * 0.6}
            height={3}
            rx={1}
            fill="rgba(255, 255, 255, 0.25)"
          />
          <rect
            x={x + blockSize * 0.15}
            y={y + blockSize * 0.4}
            width={blockSize * 0.45}
            height={3}
            rx={1}
            fill="rgba(255, 255, 255, 0.2)"
          />
          <rect
            x={x + blockSize * 0.15}
            y={y + blockSize * 0.6}
            width={blockSize * 0.55}
            height={3}
            rx={1}
            fill="rgba(255, 255, 255, 0.2)"
          />
        </g>
      );
    });
  };

  // Calculate center offsets for grids within panels
  const gridTotalSize = gridSize * blockSize + (gridSize - 1) * blockGap;
  const gridOffsetInPanel = (panelWidth - gridTotalSize) / 2;

  // Count relevant/irrelevant in AI view
  const relevantInAI = aiSeesBlocks.filter(b => b.isRelevant).length;
  const irrelevantInAI = aiSeesBlocks.filter(b => !b.isRelevant).length;
  const totalInAI = aiSeesBlocks.length;

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        opacity,
      }}
    >
      {/* Title */}
      <div
        style={{
          position: "absolute",
          top: 30,
          left: "50%",
          transform: "translateX(-50%)",
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 36,
          fontWeight: 700,
          color: COLORS.TITLE,
          textShadow: "0 2px 10px rgba(0,0,0,0.5)",
        }}
      >
        The Context Mismatch Problem
      </div>

      {/* VS divider */}
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: "50%",
          transform: "translate(-50%, -50%)",
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 48,
          fontWeight: 700,
          color: "rgba(255, 255, 255, 0.3)",
          textShadow: "0 2px 10px rgba(0,0,0,0.5)",
          zIndex: 10,
        }}
      >
        VS
      </div>

      {/* Left panel: What AI sees */}
      <div
        style={{
          position: "absolute",
          left: leftPanelX,
          top: panelTop,
          width: panelWidth,
          height: panelHeight,
          backgroundColor: "rgba(30, 30, 50, 0.9)",
          borderRadius: 16,
          border: `2px solid ${COLORS.IRRELEVANT_CODE}60`,
          overflow: "hidden",
        }}
      >
        {/* Panel header */}
        <div
          style={{
            padding: "16px 24px",
            backgroundColor: "rgba(148, 74, 74, 0.3)",
            borderBottom: `1px solid ${COLORS.IRRELEVANT_CODE}40`,
          }}
        >
          <div
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 24,
              fontWeight: 600,
              color: COLORS.IRRELEVANT_CODE,
            }}
          >
            What AI Sees
          </div>
          <div
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 14,
              color: "rgba(255, 255, 255, 0.6)",
              marginTop: 4,
            }}
          >
            {relevantInAI} relevant + {irrelevantInAI} irrelevant = {totalInAI} blocks
          </div>
        </div>

        {/* Grid */}
        <svg
          width={panelWidth}
          height={panelHeight - 80}
          style={{ marginTop: 20 }}
        >
          {renderGrid(aiSeesBlocks, gridOffsetInPanel, 20)}
        </svg>

        {/* Warning label */}
        <div
          style={{
            position: "absolute",
            bottom: 20,
            left: "50%",
            transform: "translateX(-50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 16,
            fontWeight: 500,
            color: COLORS.IRRELEVANT_CODE,
            padding: "8px 16px",
            backgroundColor: "rgba(148, 74, 74, 0.2)",
            borderRadius: 6,
            border: `1px solid ${COLORS.IRRELEVANT_CODE}40`,
          }}
        >
          "Grabbed the wrong stuff"
        </div>
      </div>

      {/* Right panel: What's actually needed */}
      <div
        style={{
          position: "absolute",
          left: rightPanelX,
          top: panelTop,
          width: panelWidth,
          height: panelHeight,
          backgroundColor: "rgba(30, 50, 40, 0.9)",
          borderRadius: 16,
          border: `2px solid ${COLORS.RELEVANT_CODE}60`,
          overflow: "hidden",
        }}
      >
        {/* Panel header */}
        <div
          style={{
            padding: "16px 24px",
            backgroundColor: "rgba(90, 170, 110, 0.2)",
            borderBottom: `1px solid ${COLORS.RELEVANT_CODE}40`,
          }}
        >
          <div
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 24,
              fontWeight: 600,
              color: COLORS.RELEVANT_CODE,
            }}
          >
            What's Actually Needed
          </div>
          <div
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 14,
              color: "rgba(255, 255, 255, 0.6)",
              marginTop: 4,
            }}
          >
            All {neededBlocks.length} relevant blocks
          </div>
        </div>

        {/* Grid */}
        <svg
          width={panelWidth}
          height={panelHeight - 80}
          style={{ marginTop: 20 }}
        >
          {renderGrid(neededBlocks, gridOffsetInPanel, 20)}
        </svg>

        {/* Success label */}
        <div
          style={{
            position: "absolute",
            bottom: 20,
            left: "50%",
            transform: "translateX(-50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 16,
            fontWeight: 500,
            color: COLORS.RELEVANT_CODE,
            padding: "8px 16px",
            backgroundColor: "rgba(90, 170, 110, 0.2)",
            borderRadius: 6,
            border: `1px solid ${COLORS.RELEVANT_CODE}40`,
          }}
        >
          Focused, relevant context
        </div>
      </div>

      {/* Legend */}
      <div
        style={{
          position: "absolute",
          bottom: 40,
          left: "50%",
          transform: "translateX(-50%)",
          display: "flex",
          gap: 40,
          padding: "12px 24px",
          backgroundColor: "rgba(26, 26, 46, 0.9)",
          borderRadius: 8,
        }}
      >
        <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
          <div
            style={{
              width: 20,
              height: 20,
              borderRadius: 4,
              backgroundColor: COLORS.RELEVANT_CODE,
            }}
          />
          <span
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 16,
              color: "rgba(255, 255, 255, 0.9)",
            }}
          >
            Relevant code
          </span>
        </div>
        <div style={{ display: "flex", alignItems: "center", gap: 12 }}>
          <div
            style={{
              width: 20,
              height: 20,
              borderRadius: 4,
              backgroundColor: COLORS.IRRELEVANT_CODE,
            }}
          />
          <span
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 16,
              color: "rgba(255, 255, 255, 0.9)",
            }}
          >
            Irrelevant code (wasted context)
          </span>
        </div>
      </div>
    </div>
  );
};
