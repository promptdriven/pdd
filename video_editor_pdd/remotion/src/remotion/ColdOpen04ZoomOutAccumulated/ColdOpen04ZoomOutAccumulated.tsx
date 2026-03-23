import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from "remotion";
import {
  BG_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  TOTAL_FRAMES,
  ZOOM_LEVELS,
  DRIFT_START_FRAME,
  DRIFT_PX_PER_FRAME,
  LAYER1_START,
  LAYER2_START,
  LAYER3_START,
  USER_SERVICE_CODE,
  AUTH_CONTROLLER_CODE,
  MINI_PANE_SNIPPETS,
  INITIAL_TABS,
  EXPANDED_TABS,
  EDITOR_BG,
  TAB_BORDER,
  TAB_HEIGHT,
  TEXT_DIM,
} from "./constants";
import { TabBar, CodeBlock, MiniCodePane } from "./CodeEditor";
import FileExplorerTree from "./FileExplorerTree";
import DiffMarkersLayer from "./DiffMarkersLayer";
import TodoLabelsLayer from "./TodoLabelsLayer";

// ── Zoom Container ──────────────────────────────────────────────────
const ZoomContainer: React.FC<{ children: React.ReactNode }> = ({
  children,
}) => {
  const frame = useCurrentFrame();

  // Build zoom interpolation from zoom levels
  const inputRange = ZOOM_LEVELS.map((z) => z.frame);
  const outputRange = ZOOM_LEVELS.map((z) => z.scale);

  const scale = interpolate(frame, inputRange, outputRange, {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Final drift after frame 140
  const driftX =
    frame > DRIFT_START_FRAME
      ? (frame - DRIFT_START_FRAME) * DRIFT_PX_PER_FRAME
      : 0;

  return (
    <div
      style={{
        position: "absolute",
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        left: "50%",
        top: "50%",
        transform: `translate(-50%, -50%) scale(${scale}) translateX(${driftX}px)`,
        transformOrigin: "center center",
      }}
    >
      {children}
    </div>
  );
};

// ── Adjacent File Panel ─────────────────────────────────────────────
const AdjacentFilePanel: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [LAYER1_START, LAYER1_START + 15],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const slideX = interpolate(
    frame,
    [LAYER1_START, LAYER1_START + 15],
    [40, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: CANVAS_WIDTH * 0.52,
        top: 0,
        width: CANVAS_WIDTH * 0.48,
        height: CANVAS_HEIGHT,
        opacity,
        transform: `translateX(${slideX}px)`,
        display: "flex",
        flexDirection: "column",
      }}
    >
      <div
        style={{
          backgroundColor: EDITOR_BG,
          flex: 1,
          borderLeft: `1px solid ${TAB_BORDER}`,
          display: "flex",
          flexDirection: "column",
        }}
      >
        {/* Mini tab */}
        <div
          style={{
            height: 28,
            backgroundColor: "#1C2128",
            borderBottom: `1px solid ${TAB_BORDER}`,
            display: "flex",
            alignItems: "center",
            padding: "0 10px",
            gap: 8,
          }}
        >
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 10,
              color: TEXT_DIM,
              opacity: 0.8,
            }}
          >
            AuthController.ts
          </span>
        </div>

        {/* Code content */}
        <div style={{ padding: "8px 0", flex: 1, overflow: "hidden" }}>
          {AUTH_CONTROLLER_CODE.map((line) => (
            <div
              key={line.lineNum}
              style={{
                display: "flex",
                height: 18,
                alignItems: "center",
                paddingLeft: 8,
              }}
            >
              <span
                style={{
                  width: 30,
                  textAlign: "right",
                  paddingRight: 8,
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: 10,
                  color: TEXT_DIM,
                  opacity: 0.4,
                  flexShrink: 0,
                }}
              >
                {line.lineNum}
              </span>
              <span
                style={{
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: 11,
                  whiteSpace: "pre",
                }}
              >
                {line.tokens.map((token, j) => (
                  <span key={j} style={{ color: token.color }}>
                    {token.text}
                  </span>
                ))}
              </span>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
};

// ── Multi-Pane Grid (Layer 3) ───────────────────────────────────────
const MultiPaneGrid: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [LAYER3_START, LAYER3_START + 15],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const scale = interpolate(
    frame,
    [LAYER3_START, LAYER3_START + 15],
    [0.9, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const paneNames = ["app.config.ts", "user.test.ts", "helpers.ts"];

  return (
    <div
      style={{
        position: "absolute",
        left: 250,
        top: CANVAS_HEIGHT + 20,
        display: "flex",
        gap: 12,
        opacity,
        transform: `scale(${scale})`,
      }}
    >
      {MINI_PANE_SNIPPETS.map((snippet, i) => (
        <MiniCodePane
          key={i}
          lines={snippet}
          title={paneNames[i]}
          width={380}
          height={140}
        />
      ))}
    </div>
  );
};

// ── Status Bar ──────────────────────────────────────────────────────
const StatusBar: React.FC = () => {
  return (
    <div
      style={{
        position: "absolute",
        bottom: 0,
        left: 0,
        right: 0,
        height: 24,
        backgroundColor: "#1F6FEB",
        display: "flex",
        alignItems: "center",
        padding: "0 12px",
        gap: 16,
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 10,
          color: "white",
          opacity: 0.9,
        }}
      >
        main
      </span>
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 10,
          color: "white",
          opacity: 0.7,
        }}
      >
        TypeScript
      </span>
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 10,
          color: "white",
          opacity: 0.7,
          marginLeft: "auto",
        }}
      >
        Ln 14, Col 42
      </span>
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 10,
          color: "white",
          opacity: 0.7,
        }}
      >
        UTF-8
      </span>
    </div>
  );
};

// ── Main Component ──────────────────────────────────────────────────
export const defaultColdOpen04ZoomOutAccumulatedProps = {};

export const ColdOpen04ZoomOutAccumulated: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine which tab bar to show based on zoom phase
  const showExpandedTabs = frame >= LAYER1_START;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      <ZoomContainer>
        {/* ── IDE Chrome: Full workspace container ── */}
        <div
          style={{
            position: "absolute",
            left: 0,
            top: 0,
            width: CANVAS_WIDTH,
            height: CANVAS_HEIGHT,
          }}
        >
          {/* Tab bar */}
          <TabBar tabs={showExpandedTabs ? EXPANDED_TABS : INITIAL_TABS} />

          {/* Main editor area */}
          <div
            style={{
              position: "absolute",
              top: TAB_HEIGHT,
              left: 0,
              right: 0,
              bottom: 24,
              display: "flex",
            }}
          >
            {/* Primary code editor (UserService.ts) */}
            <div
              style={{
                flex: showExpandedTabs ? 0.52 : 1,
                display: "flex",
                flexDirection: "column",
                transition: "flex 0.3s ease",
              }}
            >
              <CodeBlock
                lines={USER_SERVICE_CODE}
                showCursor={frame < 30}
                cursorLine={14}
              />
            </div>
          </div>

          {/* Status bar */}
          <StatusBar />
        </div>

        {/* ── Layer 1: Adjacent file (frame 15+) ── */}
        <Sequence from={LAYER1_START} layout="none">
          <AdjacentFilePanel />
        </Sequence>

        {/* ── Layer 2: File explorer tree (frame 50+) ── */}
        <Sequence from={LAYER2_START} layout="none">
          <FileExplorerTree width={220} />
        </Sequence>

        {/* ── Layer 2: Diff markers (frame 50+) ── */}
        <Sequence from={LAYER2_START} layout="none">
          <DiffMarkersLayer />
        </Sequence>

        {/* ── Layer 3: Multi-pane grid + TODO labels (frame 90+) ── */}
        <Sequence from={LAYER3_START} layout="none">
          <MultiPaneGrid />
          <TodoLabelsLayer />
        </Sequence>
      </ZoomContainer>
    </AbsoluteFill>
  );
};

export default ColdOpen04ZoomOutAccumulated;
