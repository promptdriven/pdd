import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  spring,
  useCurrentFrame,
  useVideoConfig,
} from "remotion";
import {
  COLORS,
  BEATS,
  INITIAL_NODES,
  INITIAL_EDGES,
  TANGLED_EDGES,
  WARNING_COMMENTS,
  PATCH_EVENTS,
  TIME_LABELS,
  getNodeDrift,
  CodebaseTimelapsePropsType,
  FileNode,
} from "./constants";

/**
 * CodebaseTimelapse: Time-lapse visualization of a codebase accumulating patches.
 * Shows files as nodes in a dependency graph, with patches (// HACK, // TODO, // FIXME)
 * appearing over time, edges tangling, and warning comments fading in.
 */
export const CodebaseTimelapse: React.FC<CodebaseTimelapsePropsType> = ({
  showTimeCounter = true,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  // --- NODE POSITIONS WITH DRIFT ---
  const getNodePosition = (node: FileNode, index: number) => {
    const drift = getNodeDrift(index, frame);
    return {
      x: node.x + drift.dx,
      y: node.y + drift.dy,
    };
  };

  // --- NODE APPEARANCE ---
  const nodeAppearProgress = interpolate(
    frame,
    [BEATS.CLEAN_START + 10, BEATS.CLEAN_END - 10],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // --- EDGE APPEARANCE ---
  const edgeAppearProgress = interpolate(
    frame,
    [BEATS.CLEAN_START + 40, BEATS.CLEAN_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // --- COLOR SHIFT (blue -> gray-orange -> red over time) ---
  const colorProgress = interpolate(
    frame,
    [BEATS.CLEAN_START, BEATS.YEAR1_END, BEATS.YEAR2_END, BEATS.YEAR3_END],
    [0, 0.33, 0.66, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const getNodeColor = () => {
    if (colorProgress < 0.33) return COLORS.NODE_CLEAN;
    if (colorProgress < 0.66) return COLORS.NODE_YEAR1;
    if (colorProgress < 0.85) return COLORS.NODE_YEAR2;
    return COLORS.NODE_YEAR3;
  };

  // --- PATCHES ACCUMULATED AT CURRENT FRAME ---
  const activePatchesCount = PATCH_EVENTS.filter((p) => frame >= p.frame).length;

  // Count patches per node
  const patchCountByNodeFixed = PATCH_EVENTS.reduce<Record<string, number>>((acc, p) => {
    if (frame >= p.frame) {
      acc[p.nodeId] = (acc[p.nodeId] || 0) + 1;
    }
    return acc;
  }, {});

  // --- TIME LABEL ---
  const getCurrentTimeLabel = () => {
    let currentLabel = TIME_LABELS[0].label;
    for (const tl of TIME_LABELS) {
      if (frame >= tl.frame) {
        currentLabel = tl.label;
      }
    }
    return currentLabel;
  };

  // --- ACTIVE TANGLED EDGES ---
  const activeTangledEdges = TANGLED_EDGES.filter((te) => frame >= te.appearAtFrame);

  // --- WARNING COMMENTS VISIBLE ---
  const activeComments = WARNING_COMMENTS.filter((wc) => frame >= wc.appearAtFrame);

  // --- WARNING INDICATOR (pulses red in chaos mode) ---
  const warningOpacity =
    frame >= BEATS.YEAR3_START
      ? 0.6 + 0.4 * Math.sin((frame - BEATS.YEAR3_START) * 0.2)
      : 0;

  // --- OVERALL OVERLAY TINT (shifts warmer over time) ---
  const warmOverlayOpacity = interpolate(
    frame,
    [BEATS.YEAR1_END, BEATS.YEAR3_END],
    [0, 0.08],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Helper: find node by id for edges
  const findNode = (id: string) => {
    const idx = INITIAL_NODES.findIndex((n) => n.id === id);
    if (idx === -1) return null;
    return getNodePosition(INITIAL_NODES[idx], idx);
  };

  // Hold phase subtle pulse
  const holdPulse =
    frame >= BEATS.HOLD_START
      ? 0.95 + 0.05 * Math.sin((frame - BEATS.HOLD_START) * 0.1)
      : 1;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.BACKGROUND,
      }}
    >
      {/* SVG layer for graph */}
      <svg
        width={width}
        height={height}
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          transform: `scale(${holdPulse})`,
          transformOrigin: "center center",
        }}
      >
        {/* --- INITIAL EDGES --- */}
        {edgeAppearProgress > 0 &&
          INITIAL_EDGES.map((edge, i) => {
            const fromPos = findNode(edge.from);
            const toPos = findNode(edge.to);
            if (!fromPos || !toPos) return null;

            const staggerDelay = i / INITIAL_EDGES.length;
            const edgeOpacity = interpolate(
              edgeAppearProgress,
              [staggerDelay, Math.min(staggerDelay + 0.3, 1)],
              [0, 0.6],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            );

            return (
              <line
                key={`edge-${edge.from}-${edge.to}`}
                x1={fromPos.x}
                y1={fromPos.y}
                x2={toPos.x}
                y2={toPos.y}
                stroke={COLORS.EDGE_CLEAN}
                strokeWidth={2}
                opacity={edgeOpacity}
              />
            );
          })}

        {/* --- TANGLED EDGES (appear over time) --- */}
        {activeTangledEdges.map((te) => {
          const fromPos = findNode(te.edge.from);
          const toPos = findNode(te.edge.to);
          if (!fromPos || !toPos) return null;

          const edgeAge = frame - te.appearAtFrame;
          const edgeOpacity = interpolate(edgeAge, [0, 20], [0, 0.5], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          });

          return (
            <line
              key={`tangled-${te.edge.from}-${te.edge.to}`}
              x1={fromPos.x}
              y1={fromPos.y}
              x2={toPos.x}
              y2={toPos.y}
              stroke={COLORS.EDGE_TANGLED}
              strokeWidth={1.5}
              strokeDasharray="6,4"
              opacity={edgeOpacity}
            />
          );
        })}

        {/* --- FILE NODES --- */}
        {INITIAL_NODES.map((node, i) => {
          const pos = getNodePosition(node, i);
          const staggerDelay = i / INITIAL_NODES.length;
          const nodeOpacity = interpolate(
            nodeAppearProgress,
            [staggerDelay, Math.min(staggerDelay + 0.2, 1)],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );

          const patches = patchCountByNodeFixed[node.id] || 0;
          const nodeSize = node.size + patches * 3;
          const nodeColor = patches === 0 ? getNodeColor() : COLORS.PATCH_HIGHLIGHT;
          const nodeStroke =
            patches >= 3 ? COLORS.WARNING_RED : patches > 0 ? COLORS.PATCH_HIGHLIGHT : "transparent";

          return (
            <g key={`node-${node.id}`} opacity={nodeOpacity}>
              {/* Node glow for heavily-patched nodes */}
              {patches >= 2 && (
                <circle
                  cx={pos.x}
                  cy={pos.y}
                  r={nodeSize + 8}
                  fill="none"
                  stroke={COLORS.PATCH_HIGHLIGHT}
                  strokeWidth={2}
                  opacity={0.2 + 0.1 * Math.sin(frame * 0.15 + i)}
                />
              )}

              {/* Main node circle */}
              <circle
                cx={pos.x}
                cy={pos.y}
                r={nodeSize}
                fill={nodeColor}
                opacity={0.7 + patches * 0.05}
                stroke={nodeStroke}
                strokeWidth={patches > 0 ? 2 : 0}
              />

              {/* Node label */}
              <text
                x={pos.x}
                y={pos.y + nodeSize + 18}
                textAnchor="middle"
                fill="rgba(255, 255, 255, 0.6)"
                fontSize={12}
                fontFamily="'JetBrains Mono', monospace"
              >
                {node.label}
              </text>

              {/* Patch type badges */}
              {PATCH_EVENTS.filter(
                (p) => p.nodeId === node.id && frame >= p.frame
              ).map((p, pi) => {
                const badgeAge = frame - p.frame;
                const badgeScale = spring({
                  frame: badgeAge,
                  fps: 30,
                  config: {
                    damping: 20,
                  },
                });
                const badgeOpacity = Math.min(badgeScale, 0.8);
                const angle = (pi * 2 * Math.PI) / 5 - Math.PI / 2;
                const badgeR = nodeSize + 15 + pi * 6;
                const bx = pos.x + Math.cos(angle) * badgeR;
                const by = pos.y + Math.sin(angle) * badgeR;

                const badgeColor =
                  p.type === "HACK"
                    ? "#E5853A"
                    : p.type === "TODO"
                      ? "#D9944A"
                      : "#D94A4A";

                return (
                  <g
                    key={`badge-${node.id}-${pi}`}
                    opacity={badgeOpacity}
                    transform={`translate(${bx}, ${by}) scale(${badgeScale})`}
                    style={{ transformOrigin: '0 0' }}
                  >
                    <rect
                      x={-22}
                      y={-7}
                      width={44}
                      height={14}
                      rx={3}
                      fill="rgba(0,0,0,0.7)"
                    />
                    <text
                      x={0}
                      y={4}
                      textAnchor="middle"
                      fill={badgeColor}
                      fontSize={9}
                      fontFamily="'JetBrains Mono', monospace"
                      fontWeight={600}
                    >
                      {`// ${p.type}`}
                    </text>
                  </g>
                );
              })}
            </g>
          );
        })}
      </svg>

      {/* --- WARNING COMMENTS (HTML overlay for styling) --- */}
      {activeComments.map((wc, i) => {
        const commentAge = frame - wc.appearAtFrame;
        const commentOpacity = interpolate(commentAge, [0, 30], [0, 0.9], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        });

        return (
          <div
            key={`comment-${i}`}
            style={{
              position: "absolute",
              left: wc.x,
              top: wc.y,
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: 12,
              color: COLORS.COMMENT_TEXT,
              backgroundColor: COLORS.COMMENT_BG,
              padding: "4px 8px",
              borderLeft: `3px solid ${COLORS.COMMENT_BORDER}`,
              borderRadius: "0 4px 4px 0",
              opacity: commentOpacity,
              whiteSpace: "nowrap",
              pointerEvents: "none",
            }}
          >
            {wc.text}
          </div>
        );
      })}

      {/* --- TIME COUNTER --- */}
      {showTimeCounter && (
        <div
          style={{
            position: "absolute",
            top: 40,
            right: 60,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 36,
            fontWeight: 700,
            color: COLORS.TIME_LABEL,
            textShadow: "0 2px 10px rgba(0,0,0,0.5)",
            opacity: interpolate(frame, [0, 20], [0, 1], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }),
          }}
        >
          {getCurrentTimeLabel()}
        </div>
      )}

      {/* --- PATCH COUNTER --- */}
      <div
        style={{
          position: "absolute",
          bottom: 40,
          right: 60,
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 20,
          fontWeight: 500,
          color:
            activePatchesCount > 15
              ? COLORS.WARNING_RED
              : activePatchesCount > 8
                ? COLORS.PATCH_HIGHLIGHT
                : "rgba(255, 255, 255, 0.6)",
          opacity: activePatchesCount > 0 ? 1 : 0,
          textShadow: "0 1px 6px rgba(0,0,0,0.5)",
        }}
      >
        {activePatchesCount} patches accumulated
      </div>

      {/* --- WARNING INDICATOR (Year 3+ chaos) --- */}
      {warningOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: 40,
            left: 60,
            display: "flex",
            alignItems: "center",
            gap: 10,
            opacity: warningOpacity,
          }}
        >
          <div
            style={{
              width: 16,
              height: 16,
              borderRadius: "50%",
              backgroundColor: COLORS.WARNING_RED,
              boxShadow: `0 0 12px ${COLORS.WARNING_RED}`,
            }}
          />
          <span
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 18,
              fontWeight: 600,
              color: COLORS.WARNING_RED,
              textShadow: "0 1px 6px rgba(0,0,0,0.5)",
            }}
          >
            Complexity Warning
          </span>
        </div>
      )}

      {/* --- WARM OVERLAY TINT --- */}
      {warmOverlayOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: "100%",
            height: "100%",
            backgroundColor: `rgba(217, 74, 74, ${warmOverlayOpacity})`,
            pointerEvents: "none",
          }}
        />
      )}
    </AbsoluteFill>
  );
};
