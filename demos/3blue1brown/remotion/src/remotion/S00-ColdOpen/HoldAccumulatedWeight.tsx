import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  useVideoConfig,
} from "remotion";

/**
 * HoldAccumulatedWeight (01e) — Production-path component for the 6-second
 * contemplative hold on the split-screen accumulated-weight composition.
 *
 * Renders a static split-screen scene with:
 * - Left: Complex codebase visualization with ambient animations
 * - Right: Overflowing mending workspace with breathing/shadow animations
 * - Center divider, vignette, desaturation
 *
 * All visual elements are at their "hold" state (post-zoom-out).
 */

const COLORS = {
  LEFT_BG: "#1a1a2e",
  LEFT_ACCENT: "#4A90D9",
  CODE_ADDED: "#4ade80",
  CODE_REMOVED: "#f87171",
  RIGHT_BG: "#2d2416",
  RIGHT_ACCENT: "#D9944A",
  DIVIDER: "#ffffff",
};

// File tree data (deterministic)
const FILE_DIRS = [
  { name: "src/", files: [] },
  { name: "  components/", files: ["Header.tsx", "Footer.tsx", "Sidebar.tsx", "Navigation.tsx", "Button.tsx", "Modal.tsx", "Card.tsx", "Table.tsx", "Form.tsx"] },
  { name: "  utils/", files: ["parser.ts", "helpers.ts", "validators.ts", "formatters.ts", "string-utils.ts", "date-utils.ts"] },
  { name: "  api/", files: ["routes.ts", "middleware.ts", "auth.ts", "handlers.ts", "validators.ts", "errors.ts"] },
  { name: "  services/", files: ["user-service.ts", "auth-service.ts", "data-service.ts", "cache-service.ts", "payment-service.ts"] },
  { name: "  models/", files: ["User.ts", "Session.ts", "Config.ts", "Product.ts", "Order.ts"] },
  { name: "  hooks/", files: ["useAuth.ts", "useData.ts", "useForm.ts", "useFetch.ts", "useDebounce.ts"] },
  { name: "  store/", files: ["actions.ts", "reducers.ts", "selectors.ts", "store.ts"] },
  { name: "  types/", files: ["index.ts", "api.ts", "models.ts", "components.ts"] },
];

const FLAT_FILES: Array<{ path: string; hasChanges: boolean; hasWarning: boolean }> = [];
let fileIdx = 0;
FILE_DIRS.forEach((dir) => {
  FLAT_FILES.push({ path: dir.name, hasChanges: false, hasWarning: false });
  fileIdx++;
  dir.files.forEach((f) => {
    FLAT_FILES.push({
      path: `${dir.name.replace(/\/$/, "")}  ${f}`,
      hasChanges: fileIdx % 3 === 0,
      hasWarning: fileIdx % 7 === 0,
    });
    fileIdx++;
  });
});

const TODO_COMMENTS = [
  { text: "// FIXME: memory leak", x: 15, y: 20 },
  { text: "// TODO: refactor this", x: 60, y: 35 },
  { text: "// temporary workaround", x: 25, y: 55 },
  { text: "// don't touch!", x: 70, y: 70 },
];

const MENDED_ITEMS = [
  { type: "sock", x: 15, y: 18, rotation: -15 },
  { type: "shirt", x: 68, y: 15, rotation: 10 },
  { type: "sock", x: 32, y: 22, rotation: 5 },
  { type: "trouser", x: 82, y: 20, rotation: -8 },
  { type: "sock", x: 22, y: 30, rotation: 12 },
  { type: "shirt", x: 75, y: 28, rotation: -5 },
  { type: "sock", x: 40, y: 35, rotation: -10 },
  { type: "trouser", x: 58, y: 38, rotation: 7 },
  { type: "shirt", x: 12, y: 42, rotation: -12 },
  { type: "sock", x: 85, y: 45, rotation: 15 },
  { type: "sock", x: 28, y: 48, rotation: -8 },
  { type: "shirt", x: 65, y: 52, rotation: 11 },
  { type: "trouser", x: 45, y: 55, rotation: -6 },
  { type: "sock", x: 18, y: 58, rotation: 9 },
  { type: "shirt", x: 78, y: 62, rotation: -13 },
  { type: "sock", x: 35, y: 65, rotation: 14 },
  { type: "trouser", x: 55, y: 68, rotation: -9 },
  { type: "sock", x: 70, y: 72, rotation: 6 },
  { type: "shirt", x: 25, y: 75, rotation: -11 },
  { type: "sock", x: 48, y: 78, rotation: 8 },
  { type: "sock", x: 82, y: 80, rotation: -7 },
  { type: "trouser", x: 38, y: 83, rotation: 13 },
];

const FILE_BLAME_COLORS = [
  "#5A3A3A", "#4A4A3A", "#3A4A5A", "#4A3A5A", "#3A5A4A",
];

// Small item icons
const SmallSockIcon: React.FC = () => (
  <svg width="55" height="40" viewBox="0 0 55 40">
    <path d="M 8 3 L 16 3 L 16 18 C 16 22 18 25 22 27 L 48 27 C 52 27 54 30 53 34 C 52 37 48 39 44 39 L 18 39 C 10 39 6 35 6 30 L 6 25 C 6 22 7 20 8 18 Z" fill="#C4956A" stroke="#8B6914" strokeWidth="1.5" />
    <rect x="7" y="3" width="10" height="6" fill="#A67B5B" rx="1" />
    <ellipse cx="28" cy="33" rx="8" ry="4" fill={COLORS.RIGHT_ACCENT} opacity="0.8" />
  </svg>
);

const SmallShirtIcon: React.FC = () => (
  <svg width="55" height="55" viewBox="0 0 55 55">
    <path d="M 12 12 L 20 6 L 27 12 L 34 6 L 42 12 L 38 22 L 38 48 L 16 48 L 16 22 Z" fill="#7B8B6F" stroke="#5C6B50" strokeWidth="1.5" />
    <path d="M 20 6 L 27 14 L 34 6" fill="none" stroke="#5C6B50" strokeWidth="1.5" />
    <ellipse cx="40" cy="34" rx="5" ry="7" fill={COLORS.RIGHT_ACCENT} opacity="0.8" />
  </svg>
);

const SmallTrouserIcon: React.FC = () => (
  <svg width="50" height="60" viewBox="0 0 50 60">
    <path d="M 12 6 L 38 6 L 38 22 L 32 55 L 26 55 L 25 28 L 24 55 L 18 55 L 12 22 Z" fill="#5C5C8A" stroke="#4A4A70" strokeWidth="1.5" />
    <rect x="12" y="6" width="26" height="5" fill="#4A4A70" />
    <ellipse cx="19" cy="35" rx="5" ry="6" fill={COLORS.RIGHT_ACCENT} opacity="0.8" />
  </svg>
);

const MendedItemIcon: React.FC<{ type: string }> = ({ type }) => {
  if (type === "sock") return <SmallSockIcon />;
  if (type === "shirt") return <SmallShirtIcon />;
  return <SmallTrouserIcon />;
};

interface HoldAccumulatedWeightProps {
  durationFrames: number;
}

export const HoldAccumulatedWeight: React.FC<HoldAccumulatedWeightProps> = ({
  durationFrames,
}) => {
  const frame = useCurrentFrame();
  const { width, height, fps } = useVideoConfig();

  // --- Left-side ambient animations (Issue #3 fix) ---
  // Warning icon that fades in and out periodically
  const warningCycle = (frame % (fps * 3)) / (fps * 3); // 3-second cycle
  const warningOpacity = interpolate(
    warningCycle,
    [0, 0.15, 0.3, 0.45, 1],
    [0, 0.7, 0.7, 0, 0],
  );
  // Which file gets the warning (cycles through a few positions)
  const warningFileIndex = Math.floor(frame / (fps * 3)) % 4;
  const warningPositions = [
    { x: 35, y: 25 },
    { x: 72, y: 42 },
    { x: 20, y: 60 },
    { x: 65, y: 18 },
  ];

  // Cursor blink (0.5s on, 0.5s off)
  const cursorVisible = Math.floor(frame / (fps * 0.5)) % 2 === 0;

  // New TODO that fades in mid-hold
  const newTodoProgress = interpolate(
    frame,
    [fps * 2.5, fps * 3.5],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Subtle screen flicker (very occasional, very subtle)
  const flickerAmount = (frame % (fps * 4) < 2) ? 0.03 : 0;

  // --- Right-side ambient animations (Issue #4 fix) ---
  // Grandmother breathing (subtle Y oscillation, ~4 second cycle)
  const breathingOffset = Math.sin((frame / fps) * Math.PI * 0.5) * 2;

  // Lamp shadow movement (subtle opacity oscillation synced to flame)
  const shadowPulse = 0.5 + Math.sin((frame / fps) * Math.PI * 4) * 0.08;

  // Lamp glow size oscillation
  const glowScale = 1 + Math.sin((frame / fps) * Math.PI * 4) * 0.03;

  return (
    <AbsoluteFill style={{ filter: "saturate(85%)" }}>
      {/* ===== LEFT PANEL: Developer / Codebase ===== */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: width / 2,
          height,
          overflow: "hidden",
          backgroundColor: COLORS.LEFT_BG,
        }}
      >
        {/* Subtle screen flicker overlay */}
        {flickerAmount > 0 && (
          <div
            style={{
              position: "absolute",
              inset: 0,
              backgroundColor: `rgba(74, 144, 217, ${flickerAmount})`,
              pointerEvents: "none",
              zIndex: 10,
            }}
          />
        )}

        {/* IDE mockup at zoomed-out scale */}
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%) scale(0.3) translateY(-100px)",
            width: "90%",
            transformOrigin: "center center",
          }}
        >
          <div
            style={{
              backgroundColor: "#0d0d1a",
              borderRadius: 12,
              padding: 20,
              boxShadow: "0 8px 32px rgba(0,0,0,0.5)",
            }}
          >
            {/* Title bar */}
            <div style={{ display: "flex", alignItems: "center", marginBottom: 16, gap: 8 }}>
              <div style={{ width: 12, height: 12, borderRadius: "50%", backgroundColor: "#ff5f57" }} />
              <div style={{ width: 12, height: 12, borderRadius: "50%", backgroundColor: "#febc2e" }} />
              <div style={{ width: 12, height: 12, borderRadius: "50%", backgroundColor: "#28c840" }} />
              <span style={{ marginLeft: 12, color: "#666", fontFamily: "SF Mono, monospace", fontSize: 14 }}>
                parser.ts - Cursor
              </span>
            </div>
            {/* Code content */}
            <div style={{ fontFamily: "JetBrains Mono, SF Mono, monospace", fontSize: 16, lineHeight: 1.8, color: COLORS.CODE_ADDED }}>
              <div style={{ display: "flex", alignItems: "center" }}>
                <span style={{ width: 24 }} />
                <span style={{ color: "#666", width: 30, textAlign: "right", marginRight: 12 }}>1</span>
                <span style={{ color: "#e0e0e0" }}>{"function parseUserData(input) {"}</span>
              </div>
              <div style={{ display: "flex", alignItems: "center" }}>
                <span style={{ width: 24 }} />
                <span style={{ color: "#666", width: 30, textAlign: "right", marginRight: 12 }}>2</span>
                <span style={{ color: "#e0e0e0" }}>{"  const data = JSON.parse(input);"}</span>
              </div>
              <div style={{ display: "flex", alignItems: "center" }}>
                <span style={{ width: 24 }} />
                <span style={{ color: "#666", width: 30, textAlign: "right", marginRight: 12 }}>3</span>
                <span style={{ color: "#e0e0e0" }}>{"  return data?.user?.name ?? 'Unknown';"}</span>
                {/* Blinking cursor */}
                <span style={{ opacity: cursorVisible ? 1 : 0, color: COLORS.LEFT_ACCENT, marginLeft: 2 }}>|</span>
              </div>
              <div style={{ display: "flex", alignItems: "center" }}>
                <span style={{ width: 24 }} />
                <span style={{ color: "#666", width: 30, textAlign: "right", marginRight: 12 }}>4</span>
                <span style={{ color: "#e0e0e0" }}>{"}"}</span>
              </div>
            </div>
          </div>
        </div>

        {/* File tree */}
        <div
          style={{
            position: "absolute",
            top: 60,
            left: 30,
            opacity: 0.9,
            fontFamily: "JetBrains Mono, SF Mono, monospace",
            fontSize: 10,
            color: "#888",
            maxHeight: "80%",
            overflow: "hidden",
          }}
        >
          {FLAT_FILES.map((item, i) => {
            const isFolder = item.path.endsWith("/");
            return (
              <div
                key={i}
                style={{
                  display: "flex",
                  alignItems: "center",
                  gap: 4,
                  marginBottom: 1,
                }}
              >
                {/* Diff marker (deterministic colors — Issue #7 fix) */}
                {!isFolder && item.hasChanges && (
                  <div
                    style={{
                      width: 5,
                      height: 5,
                      borderRadius: "50%",
                      backgroundColor: i % 2 === 0 ? COLORS.CODE_ADDED : COLORS.CODE_REMOVED,
                      flexShrink: 0,
                    }}
                  />
                )}
                {!isFolder && !item.hasChanges && (
                  <div
                    style={{
                      width: 2,
                      height: 10,
                      backgroundColor: FILE_BLAME_COLORS[i % FILE_BLAME_COLORS.length],
                      borderRadius: 1,
                      flexShrink: 0,
                    }}
                  />
                )}
                {!isFolder && item.hasWarning && (
                  <span style={{ fontSize: 8, flexShrink: 0 }}>&#x1F525;</span>
                )}
                <span style={{ fontSize: isFolder ? 10 : 9 }}>{item.path}</span>
              </div>
            );
          })}
        </div>

        {/* Floating TODO comments */}
        {TODO_COMMENTS.map((todo, i) => (
          <div
            key={i}
            style={{
              position: "absolute",
              left: `${todo.x}%`,
              top: `${todo.y}%`,
              opacity: 0.85,
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

        {/* Ambient: New TODO fading in mid-hold */}
        {newTodoProgress > 0 && (
          <div
            style={{
              position: "absolute",
              left: "45%",
              top: "48%",
              opacity: newTodoProgress * 0.8,
              fontFamily: "JetBrains Mono, monospace",
              fontSize: 11,
              color: "#fbbf24",
              backgroundColor: "rgba(251, 191, 36, 0.12)",
              padding: "4px 8px",
              borderRadius: 4,
              transform: "rotate(-3deg)",
            }}
          >
            {"// TODO: fix race condition"}
          </div>
        )}

        {/* Ambient: Warning icon appearing and disappearing */}
        <div
          style={{
            position: "absolute",
            left: `${warningPositions[warningFileIndex].x}%`,
            top: `${warningPositions[warningFileIndex].y}%`,
            opacity: warningOpacity,
            fontSize: 14,
            pointerEvents: "none",
          }}
        >
          &#9888;
        </div>

        {/* Dependency graph */}
        <svg
          style={{
            position: "absolute",
            top: "20%",
            right: "10%",
            opacity: 0.5,
          }}
          width="250"
          height="200"
          viewBox="0 0 250 200"
        >
          {[
            { x: 30, y: 30 }, { x: 120, y: 20 }, { x: 210, y: 40 },
            { x: 50, y: 90 }, { x: 140, y: 100 }, { x: 220, y: 85 },
            { x: 40, y: 150 }, { x: 130, y: 160 }, { x: 200, y: 170 },
          ].map((node, i) => (
            <circle key={`node-${i}`} cx={node.x} cy={node.y} r="6" fill={COLORS.LEFT_ACCENT} opacity="0.7" />
          ))}
          <path d="M 30 30 Q 75 50 120 20" stroke="#f87171" strokeWidth="1.5" fill="none" opacity="0.6" />
          <path d="M 120 20 Q 165 30 210 40" stroke="#4ade80" strokeWidth="1.5" fill="none" opacity="0.6" />
          <path d="M 30 30 Q 40 60 50 90" stroke="#fbbf24" strokeWidth="1.5" fill="none" opacity="0.6" />
          <path d="M 210 40 Q 215 60 220 85" stroke="#f87171" strokeWidth="1.5" fill="none" opacity="0.6" />
          <path d="M 50 90 Q 95 95 140 100" stroke="#4ade80" strokeWidth="1.5" fill="none" opacity="0.6" />
          <path d="M 140 100 Q 180 90 220 85" stroke="#fbbf24" strokeWidth="1.5" fill="none" opacity="0.6" />
          <path d="M 50 90 Q 45 120 40 150" stroke="#f87171" strokeWidth="1.5" fill="none" opacity="0.6" />
          <path d="M 140 100 Q 135 130 130 160" stroke="#4ade80" strokeWidth="1.5" fill="none" opacity="0.6" />
          <path d="M 220 85 Q 210 125 200 170" stroke="#fbbf24" strokeWidth="1.5" fill="none" opacity="0.6" />
          <path d="M 30 30 Q 120 110 200 170" stroke="#a855f7" strokeWidth="1" fill="none" opacity="0.4" strokeDasharray="3,3" />
          <path d="M 210 40 Q 100 80 40 150" stroke="#ec4899" strokeWidth="1" fill="none" opacity="0.4" strokeDasharray="3,3" />
          <path d="M 120 20 Q 80 140 130 160" stroke="#06b6d4" strokeWidth="1" fill="none" opacity="0.4" strokeDasharray="3,3" />
        </svg>

        {/* Browser tabs */}
        <div style={{ position: "absolute", top: 20, left: 20, opacity: 0.7 }}>
          {[0, 1, 2, 3, 4].map((i) => (
            <div
              key={i}
              style={{
                display: "inline-block",
                width: 80,
                height: 24,
                backgroundColor: i === 0 ? "#0d0d1a" : "#1a1a2e",
                borderRadius: "6px 6px 0 0",
                marginRight: 2,
                padding: "4px 8px",
                fontSize: 9,
                color: "#666",
                fontFamily: "SF Mono, monospace",
                border: i === 0 ? `1px solid ${COLORS.LEFT_ACCENT}` : "1px solid #2a2a3e",
                borderBottom: "none",
                overflow: "hidden",
                whiteSpace: "nowrap",
                textOverflow: "ellipsis",
              }}
            >
              {i === 0 ? "parser.ts" : `file${i + 1}.tsx`}
            </div>
          ))}
        </div>

        {/* Developer silhouette */}
        <div
          style={{
            position: "absolute",
            bottom: 40,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: 0.6,
          }}
        >
          <svg width="60" height="60" viewBox="0 0 24 24" fill={COLORS.LEFT_ACCENT}>
            <path d="M12 4a4 4 0 0 1 4 4 4 4 0 0 1-4 4 4 4 0 0 1-4-4 4 4 0 0 1 4-4m0 10c4.42 0 8 1.79 8 4v2H4v-2c0-2.21 3.58-4 8-4z" />
          </svg>
        </div>
      </div>

      {/* ===== RIGHT PANEL: Grandmother / Mending ===== */}
      <div
        style={{
          position: "absolute",
          right: 0,
          top: 0,
          width: width / 2,
          height,
          overflow: "hidden",
          backgroundColor: COLORS.RIGHT_BG,
        }}
      >
        {/* Warm ambient light gradient with shadow pulse */}
        <div
          style={{
            position: "absolute",
            top: 0,
            right: 0,
            width: "70%",
            height: "70%",
            background: `radial-gradient(ellipse at 75% 15%, ${COLORS.RIGHT_ACCENT}40 0%, transparent 55%)`,
            opacity: shadowPulse + 0.5,
            transform: `scale(${glowScale})`,
            transformOrigin: "75% 15%",
            pointerEvents: "none",
          }}
        />

        {/* Wooden table at zoomed-out scale */}
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, -50%) scale(0.35) translateY(-80px)",
            transformOrigin: "center center",
          }}
        >
          <div
            style={{
              position: "relative",
              width: 450,
              height: 400,
              backgroundColor: "#3D3220",
              borderRadius: 10,
              boxShadow: "0 10px 40px rgba(0,0,0,0.6)",
              padding: 30,
              backgroundImage: "linear-gradient(90deg, rgba(0,0,0,0.1) 1px, transparent 1px)",
              backgroundSize: "20px 20px",
            }}
          >
            {/* Oil lamp */}
            <div style={{ position: "absolute", top: -80, right: 20 }}>
              <svg width="70" height="120" viewBox="0 0 70 120">
                <ellipse cx="35" cy="105" rx="28" ry="10" fill="#8B4513" />
                <path d="M 15 105 L 20 55 L 50 55 L 55 105" fill="#CD853F" stroke="#8B4513" strokeWidth="2" />
                <ellipse cx="35" cy="55" rx="18" ry="8" fill="#B8860B" />
                <path d="M 22 55 C 20 45 18 35 18 20 C 18 8 52 8 52 20 C 52 35 50 45 48 55" fill="rgba(255,220,150,0.15)" stroke="rgba(255,255,255,0.25)" strokeWidth="1" />
                <ellipse cx="35" cy="35" rx="10" ry="18" fill="#FFD700" opacity="0.9">
                  <animate attributeName="ry" values="18;20;18" dur="0.5s" repeatCount="indefinite" />
                </ellipse>
                <ellipse cx="35" cy="33" rx="6" ry="12" fill="#FFA500" />
                <ellipse cx="35" cy="30" rx="3" ry="8" fill="#FF6B35" />
              </svg>
              {/* Glow with shadow pulse */}
              <div
                style={{
                  position: "absolute",
                  top: 0,
                  left: -30,
                  width: 130,
                  height: 130,
                  background: `radial-gradient(circle, ${COLORS.RIGHT_ACCENT}55 0%, transparent 65%)`,
                  opacity: shadowPulse + 0.5,
                  transform: `scale(${glowScale})`,
                  pointerEvents: "none",
                }}
              />
            </div>

            {/* Completed sock */}
            <div style={{ position: "absolute", left: "50%", top: "45%", transform: "translate(-50%, -50%)" }}>
              <svg width="280" height="200" viewBox="0 0 280 200" style={{ filter: "drop-shadow(3px 6px 8px rgba(0,0,0,0.4))" }}>
                <path d="M 40 15 L 70 15 L 70 95 C 70 115 75 130 95 140 L 240 140 C 265 140 275 155 270 170 C 265 185 245 190 220 190 L 80 190 C 50 190 30 175 30 155 L 30 130 C 30 115 35 105 40 95 L 40 15 Z" fill="#C4956A" stroke="#8B6914" strokeWidth="3" />
                <rect x="38" y="15" width="34" height="30" fill="#A67B5B" rx="2" />
                {/* Darning patch (fully mended) */}
                <g transform="translate(100, 155)">
                  <g opacity="1">
                    {[-20, -12, -4, 4, 12, 20].map((x, i) => (
                      <line key={`v${i}`} x1={30 + x} y1={-2} x2={30 + x} y2={26} stroke={COLORS.RIGHT_ACCENT} strokeWidth="2.5" strokeLinecap="round" />
                    ))}
                    {[-8, -2, 4, 10, 16, 22].map((y, i) => (
                      <path key={`h${i}`} d={`M 5 ${y} Q 20 ${y + (i % 2 === 0 ? -2 : 2)} 30 ${y} Q 40 ${y + (i % 2 === 0 ? 2 : -2)} 55 ${y}`} stroke="#E8A848" strokeWidth="2" fill="none" strokeLinecap="round" />
                    ))}
                  </g>
                </g>
              </svg>
            </div>

            {/* Thread spool */}
            <div style={{ position: "absolute", bottom: 30, left: 40 }}>
              <svg width="50" height="50" viewBox="0 0 50 50">
                <ellipse cx="25" cy="40" rx="20" ry="8" fill="#3D2817" />
                <rect x="8" y="15" width="34" height="25" fill={COLORS.RIGHT_ACCENT} />
                <ellipse cx="25" cy="15" rx="17" ry="7" fill="#E8A848" />
                <ellipse cx="25" cy="40" rx="17" ry="7" fill="#B87A28" />
              </svg>
            </div>
          </div>
        </div>

        {/* Mended items scattered across the scene */}
        {MENDED_ITEMS.map((item, i) => (
          <div
            key={i}
            style={{
              position: "absolute",
              left: `${item.x}%`,
              top: `${item.y}%`,
              opacity: 0.85,
              transform: `rotate(${item.rotation}deg)`,
            }}
          >
            <MendedItemIcon type={item.type} />
          </div>
        ))}

        {/* Wicker basket */}
        <div
          style={{
            position: "absolute",
            bottom: 25,
            right: 25,
            opacity: 0.8,
          }}
        >
          <svg width="110" height="80" viewBox="0 0 110 80">
            <path d="M 10 25 C 10 10 100 10 100 25 L 95 70 C 95 78 15 78 15 70 Z" fill="#6B5344" stroke="#4A3828" strokeWidth="2" />
            {[0, 12, 24, 36, 48].map((y) => (
              <path key={y} d={`M 15 ${28 + y} Q 55 ${33 + y} 95 ${28 + y}`} fill="none" stroke="#4A3828" strokeWidth="1.5" />
            ))}
            <path d="M 35 25 Q 55 -5 75 25" fill="none" stroke="#5C4A36" strokeWidth="4" />
          </svg>
        </div>

        {/* Grandmother silhouette with breathing animation */}
        <div
          style={{
            position: "absolute",
            bottom: 35,
            left: "50%",
            transform: `translateX(-50%) translateY(${breathingOffset}px)`,
            opacity: 0.6,
          }}
        >
          <svg width="55" height="70" viewBox="0 0 55 70" fill={COLORS.RIGHT_ACCENT}>
            <circle cx="27" cy="12" r="11" />
            <ellipse cx="27" cy="5" rx="7" ry="5" /> {/* Hair bun */}
            <path d="M 15 23 C 8 25 5 40 8 65 L 46 65 C 49 40 46 25 39 23 C 35 22 30 25 27 25 C 24 25 19 22 15 23 Z" />
          </svg>
        </div>
      </div>

      {/* ===== Center divider line ===== */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: 0,
          width: 2,
          height: "100%",
          backgroundColor: COLORS.DIVIDER,
          transform: "translateX(-50%)",
          boxShadow: "0 0 10px rgba(255,255,255,0.3)",
        }}
      />

      {/* ===== Vignette overlay ===== */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          background: "radial-gradient(ellipse at center, transparent 40%, rgba(0,0,0,0.4) 100%)",
          pointerEvents: "none",
        }}
      />
    </AbsoluteFill>
  );
};
