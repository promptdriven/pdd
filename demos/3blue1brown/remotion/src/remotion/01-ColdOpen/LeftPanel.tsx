import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  useVideoConfig,
  Easing,
} from "remotion";
import { COLORS, BEATS, secondsToFrames } from "./constants";

const TODO_COMMENTS = [
  { text: "// FIXME: memory leak", x: 15, y: 20 },
  { text: "// TODO: refactor this", x: 60, y: 35 },
  { text: "// temporary workaround", x: 25, y: 55 },
  { text: "// don't touch!", x: 70, y: 70 },
];

const FILE_TREE = [
  "src/",
  "  components/",
  "    Header.tsx",
  "    Footer.tsx",
  "    Sidebar.tsx",
  "    Navigation.tsx",
  "    Button.tsx",
  "    Input.tsx",
  "    Modal.tsx",
  "    Card.tsx",
  "    Table.tsx",
  "    Form.tsx",
  "  utils/",
  "    parser.ts",
  "    helpers.ts",
  "    validators.ts",
  "    formatters.ts",
  "    string-utils.ts",
  "    date-utils.ts",
  "    array-utils.ts",
  "  api/",
  "    routes.ts",
  "    middleware.ts",
  "    auth.ts",
  "    handlers.ts",
  "    validators.ts",
  "  services/",
  "    user-service.ts",
  "    auth-service.ts",
  "    data-service.ts",
  "    cache-service.ts",
  "  models/",
  "    User.ts",
  "    Session.ts",
  "    Config.ts",
  "  hooks/",
  "    useAuth.ts",
  "    useData.ts",
  "    useForm.ts",
  "  store/",
  "    actions.ts",
  "    reducers.ts",
  "    selectors.ts",
  "  types/",
  "    index.ts",
  "    api.ts",
  "    models.ts",
  "  config/",
  "    app-config.ts",
  "    env.ts",
  "  lib/",
  "    client.ts",
  "    server.ts",
  "  index.ts",
  "  App.tsx",
];

// Git blame colors for file tree items (simulating patch history)
const FILE_BLAME_COLORS = [
  "#5A3A3A", "#4A4A3A", "#3A4A5A", "#4A3A5A", "#3A5A4A",
  "#5A4A3A", "#3A3A5A", "#5A5A3A", "#4A5A3A", "#5A3A4A",
];

export const LeftPanel: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const syncStart = secondsToFrames(BEATS.SYNC_COMPLETION_START);
  const syncEnd = secondsToFrames(BEATS.SYNC_COMPLETION_END);
  const zoomStart = secondsToFrames(BEATS.ZOOM_OUT_START);
  const zoomEnd = secondsToFrames(BEATS.ZOOM_OUT_END);

  // Phase 1: Show original code (0:00 - 0:08)
  // Phase 2: Show diff with red/green (0:08 - 0:12)
  // Phase 3: Accept changes - red fades out, green stays (0:12 - 0:15)

  // Diff appears at sync start
  const diffOpacity = interpolate(
    frame,
    [syncStart, syncStart + fps * 0.5],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Red line fades out when accepting (0:12 - 0:14)
  const acceptStart = syncStart + fps * 4;
  const redLineOpacity = interpolate(
    frame,
    [acceptStart, acceptStart + fps * 1],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Green highlight fades after acceptance
  const greenHighlightOpacity = interpolate(
    frame,
    [syncEnd, syncEnd + fps * 2],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Success checkmark (appears at 0:15)
  const checkmarkOpacity = interpolate(
    frame,
    [syncEnd, syncEnd + fps * 0.5],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Zoom out animation with three-phase easing
  // Phase 1: Ease-in (0:18-0:20, 2 seconds)
  // Phase 2: Constant speed (0:20-0:28, 8 seconds)
  // Phase 3: Ease-out (0:28-0:32, 4 seconds)
  const easeInEnd = zoomStart + fps * 2;
  const constantEnd = zoomStart + fps * 10;

  let zoomProgress = 0;
  if (frame < zoomStart) {
    zoomProgress = 0;
  } else if (frame < easeInEnd) {
    // Ease-in phase (0-2s): slow start
    const phaseProgress = (frame - zoomStart) / (fps * 2);
    zoomProgress = Easing.in(Easing.cubic)(phaseProgress) * 0.143; // 0-14.3% of total zoom
  } else if (frame < constantEnd) {
    // Constant phase (2-10s): steady movement
    const phaseProgress = (frame - easeInEnd) / (fps * 8);
    zoomProgress = 0.143 + phaseProgress * 0.714; // 14.3%-85.7% of total zoom
  } else if (frame <= zoomEnd) {
    // Ease-out phase (10-14s): slow to stop
    const phaseProgress = (frame - constantEnd) / (fps * 4);
    zoomProgress = 0.857 + Easing.out(Easing.cubic)(phaseProgress) * 0.143; // 85.7%-100%
  } else {
    zoomProgress = 1;
  }

  const scale = interpolate(zoomProgress, [0, 1], [1, 0.3]);
  const translateY = interpolate(zoomProgress, [0, 1], [0, -100]);

  const fileTreeOpacity = interpolate(zoomProgress, [0.2, 0.5], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const todoOpacity = interpolate(zoomProgress, [0.4, 0.7], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Show original code before diff appears
  const showOriginal = frame < syncStart;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.LEFT_BG,
        overflow: "hidden",
      }}
    >
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: "50%",
          transform: `translate(-50%, -50%) scale(${scale}) translateY(${translateY}px)`,
          width: "90%",
          transformOrigin: "center center",
        }}
      >
        {/* Cursor IDE mockup */}
        <div
          style={{
            backgroundColor: "#0d0d1a",
            borderRadius: 12,
            padding: 20,
            boxShadow: "0 8px 32px rgba(0,0,0,0.5)",
          }}
        >
          {/* Title bar */}
          <div
            style={{
              display: "flex",
              alignItems: "center",
              marginBottom: 16,
              gap: 8,
            }}
          >
            <div style={{ width: 12, height: 12, borderRadius: "50%", backgroundColor: "#ff5f57" }} />
            <div style={{ width: 12, height: 12, borderRadius: "50%", backgroundColor: "#febc2e" }} />
            <div style={{ width: 12, height: 12, borderRadius: "50%", backgroundColor: "#28c840" }} />
            <span style={{ marginLeft: 12, color: "#666", fontFamily: "SF Mono, monospace", fontSize: 14 }}>
              parser.ts - Cursor
            </span>
            {/* AI indicator */}
            {diffOpacity > 0 && (
              <span
                style={{
                  marginLeft: "auto",
                  color: "#a855f7",
                  fontFamily: "SF Mono, monospace",
                  fontSize: 12,
                  opacity: diffOpacity,
                  display: "flex",
                  alignItems: "center",
                  gap: 6,
                }}
              >
                <span style={{ fontSize: 16 }}>✨</span> AI Suggestion
              </span>
            )}
          </div>

          {/* Code content with diff view */}
          <div
            style={{
              fontFamily: "JetBrains Mono, SF Mono, Consolas, monospace",
              fontSize: 16,
              lineHeight: 1.8,
              color: COLORS.CODE_NORMAL,
            }}
          >
            {showOriginal ? (
              // Original code before diff
              <>
                <CodeLine lineNum={1} text="function parseUserData(input) {" />
                <CodeLine lineNum={2} text="  const data = JSON.parse(input);" />
                <CodeLine lineNum={3} text="  return data.user.name;" />
                <CodeLine lineNum={4} text="}" />
              </>
            ) : (
              // Diff view
              <>
                <CodeLine lineNum={1} text="function parseUserData(input) {" />
                <CodeLine lineNum={2} text="  const data = JSON.parse(input);" />

                {/* Removed line (red) */}
                <div
                  style={{
                    opacity: diffOpacity * redLineOpacity,
                    backgroundColor: "rgba(248, 113, 113, 0.2)",
                    marginLeft: -20,
                    marginRight: -20,
                    paddingLeft: 20,
                    paddingRight: 20,
                    display: "flex",
                    alignItems: "center",
                  }}
                >
                  <span
                    style={{
                      color: COLORS.CODE_REMOVED,
                      fontWeight: "bold",
                      width: 24,
                      textAlign: "center",
                    }}
                  >
                    −
                  </span>
                  <span style={{ color: "#666", width: 30, textAlign: "right", marginRight: 12 }}>3</span>
                  <span style={{ color: COLORS.CODE_REMOVED }}>  return data.user.name;</span>
                </div>

                {/* Added line (green) */}
                <div
                  style={{
                    opacity: diffOpacity,
                    backgroundColor: greenHighlightOpacity > 0 ? `rgba(74, 222, 128, ${0.2 * greenHighlightOpacity})` : "transparent",
                    marginLeft: -20,
                    marginRight: -20,
                    paddingLeft: 20,
                    paddingRight: 20,
                    display: "flex",
                    alignItems: "center",
                  }}
                >
                  <span
                    style={{
                      color: COLORS.CODE_ADDED,
                      fontWeight: "bold",
                      width: 24,
                      textAlign: "center",
                      opacity: greenHighlightOpacity,
                    }}
                  >
                    +
                  </span>
                  <span style={{ color: "#666", width: 30, textAlign: "right", marginRight: 12 }}>3</span>
                  <span style={{ color: greenHighlightOpacity > 0 ? COLORS.CODE_ADDED : COLORS.CODE_NORMAL }}>
                    {"  return data?.user?.name ?? 'Unknown';"}
                  </span>
                </div>

                <CodeLine lineNum={4} text="}" />

                {/* Accept button */}
                {redLineOpacity > 0 && (
                  <div
                    style={{
                      marginTop: 16,
                      display: "flex",
                      gap: 12,
                      opacity: diffOpacity * redLineOpacity,
                    }}
                  >
                    <button
                      style={{
                        backgroundColor: COLORS.CODE_ADDED,
                        color: "#000",
                        border: "none",
                        borderRadius: 6,
                        padding: "8px 16px",
                        fontFamily: "SF Mono, monospace",
                        fontSize: 13,
                        fontWeight: "bold",
                        cursor: "pointer",
                        display: "flex",
                        alignItems: "center",
                        gap: 6,
                      }}
                    >
                      ✓ Accept
                      <span style={{ opacity: 0.7, fontSize: 11 }}>Tab</span>
                    </button>
                    <button
                      style={{
                        backgroundColor: "transparent",
                        color: "#888",
                        border: "1px solid #444",
                        borderRadius: 6,
                        padding: "8px 16px",
                        fontFamily: "SF Mono, monospace",
                        fontSize: 13,
                        cursor: "pointer",
                      }}
                    >
                      ✗ Reject
                    </button>
                  </div>
                )}
              </>
            )}
          </div>

          {/* Success indicator */}
          {checkmarkOpacity > 0 && (
            <div
              style={{
                position: "absolute",
                top: 20,
                right: 20,
                opacity: checkmarkOpacity,
                display: "flex",
                alignItems: "center",
                gap: 8,
                color: COLORS.CODE_ADDED,
                fontSize: 16,
                fontFamily: "SF Mono, monospace",
              }}
            >
              <svg width="24" height="24" viewBox="0 0 24 24" fill="none">
                <circle cx="12" cy="12" r="10" fill={COLORS.CODE_ADDED} />
                <path d="M8 12l3 3 5-6" stroke="white" strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" />
              </svg>
              Patched
            </div>
          )}
        </div>
      </div>

      {/* File tree (appears during zoom out) */}
      {fileTreeOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: 60,
            left: 30,
            opacity: fileTreeOpacity,
            fontFamily: "JetBrains Mono, SF Mono, monospace",
            fontSize: 12,
            color: "#888",
          }}
        >
          {FILE_TREE.map((item, i) => (
            <div
              key={i}
              style={{
                display: "flex",
                alignItems: "center",
                gap: 6,
                opacity: interpolate(zoomProgress, [0.2 + i * 0.01, 0.3 + i * 0.01], [0, 1], {
                  extrapolateLeft: "clamp",
                  extrapolateRight: "clamp",
                }),
              }}
            >
              {/* Git blame color strip (for files, not folders) */}
              {!item.endsWith("/") && (
                <div
                  style={{
                    width: 3,
                    height: 12,
                    backgroundColor: FILE_BLAME_COLORS[i % FILE_BLAME_COLORS.length],
                    borderRadius: 1,
                  }}
                />
              )}
              <span>{item}</span>
            </div>
          ))}
        </div>
      )}

      {/* Floating TODO comments */}
      {todoOpacity > 0 &&
        TODO_COMMENTS.map((todo, i) => (
          <div
            key={i}
            style={{
              position: "absolute",
              left: `${todo.x}%`,
              top: `${todo.y}%`,
              opacity: todoOpacity * interpolate(zoomProgress, [0.4 + i * 0.05, 0.5 + i * 0.05], [0, 1], {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              }),
              fontFamily: "JetBrains Mono, monospace",
              fontSize: 11,
              color: "#f87171",
              backgroundColor: "rgba(248, 113, 113, 0.15)",
              padding: "4px 8px",
              borderRadius: 4,
              transform: `rotate(${(i % 2 === 0 ? 1 : -1) * 5}deg)`,
            }}
          >
            {todo.text}
          </div>
        ))}

      {/* Developer silhouette */}
      {zoomProgress > 0.5 && (
        <div
          style={{
            position: "absolute",
            bottom: 40,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: interpolate(zoomProgress, [0.5, 0.8], [0, 0.6], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }),
          }}
        >
          <svg width="60" height="60" viewBox="0 0 24 24" fill="#4A90D9">
            <path d="M12 4a4 4 0 0 1 4 4 4 4 0 0 1-4 4 4 4 0 0 1-4-4 4 4 0 0 1 4-4m0 10c4.42 0 8 1.79 8 4v2H4v-2c0-2.21 3.58-4 8-4z" />
          </svg>
        </div>
      )}
    </AbsoluteFill>
  );
};

// Simple code line component
const CodeLine: React.FC<{ lineNum: number; text: string }> = ({ lineNum, text }) => (
  <div style={{ display: "flex", alignItems: "center" }}>
    <span style={{ width: 24 }} />
    <span style={{ color: "#666", width: 30, textAlign: "right", marginRight: 12 }}>{lineNum}</span>
    <span>{text}</span>
  </div>
);
