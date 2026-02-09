import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  useVideoConfig,
  Easing,
} from "remotion";
import { COLORS, BEATS, secondsToFrames } from "./constants";

// Mended items for the zoom-out reveal
const MENDED_ITEMS = [
  { type: "sock", x: 20, y: 25, rotation: -15 },
  { type: "shirt", x: 70, y: 20, rotation: 10 },
  { type: "sock", x: 35, y: 45, rotation: 5 },
  { type: "trouser", x: 65, y: 50, rotation: -8 },
  { type: "sock", x: 25, y: 65, rotation: 12 },
  { type: "shirt", x: 75, y: 70, rotation: -5 },
];

// Side-view sock SVG - classic L-shape profile
const WoolSock: React.FC<{
  holeProgress: number;
  scale?: number;
}> = ({ holeProgress, scale = 1 }) => {
  const width = 280 * scale;
  const height = 200 * scale;

  return (
    <svg width={width} height={height} viewBox="0 0 280 200" style={{ filter: "drop-shadow(3px 6px 8px rgba(0,0,0,0.4))" }}>
      <defs>
        <pattern id="woolTexture" patternUnits="userSpaceOnUse" width="6" height="6">
          <circle cx="2" cy="2" r="0.8" fill="rgba(0,0,0,0.08)" />
          <circle cx="5" cy="5" r="0.8" fill="rgba(0,0,0,0.08)" />
        </pattern>
      </defs>

      {/* Main sock shape - SIDE VIEW L-shape */}
      {/* Leg goes down, then curves into foot going right */}
      <path
        d="M 40 15
           L 70 15
           L 70 95
           C 70 115 75 130 95 140
           L 240 140
           C 265 140 275 155 270 170
           C 265 185 245 190 220 190
           L 80 190
           C 50 190 30 175 30 155
           L 30 130
           C 30 115 35 105 40 95
           L 40 15
           Z"
        fill="#C4956A"
        stroke="#8B6914"
        strokeWidth="3"
      />

      {/* Wool texture overlay */}
      <path
        d="M 40 15
           L 70 15
           L 70 95
           C 70 115 75 130 95 140
           L 240 140
           C 265 140 275 155 270 170
           C 265 185 245 190 220 190
           L 80 190
           C 50 190 30 175 30 155
           L 30 130
           C 30 115 35 105 40 95
           L 40 15
           Z"
        fill="url(#woolTexture)"
      />

      {/* Ribbed cuff at top of leg */}
      <rect x="38" y="15" width="34" height="30" fill="#A67B5B" rx="2" />
      {[0, 6, 12, 18, 24].map((y) => (
        <line key={y} x1="40" y1={17 + y} x2="70" y2={17 + y} stroke="#8B6914" strokeWidth="1.5" opacity="0.5" />
      ))}

      {/* Heel reinforcement - darker area at the back of foot */}
      <ellipse cx="55" cy="150" rx="25" ry="30" fill="#A67B5B" opacity="0.5" />

      {/* Toe area - rounded front */}
      <ellipse cx="250" cy="165" rx="25" ry="22" fill="#A67B5B" opacity="0.4" />

      {/* THE HOLE - on the heel/bottom area */}
      <g transform="translate(100, 155)">
        {/* Dark hole (fades out as darning progresses) */}
        <ellipse
          cx="30"
          cy="12"
          rx="28"
          ry="14"
          fill="#2d2416"
          opacity={1 - holeProgress}
          stroke="#1a1510"
          strokeWidth="2"
        />

        {/* Frayed edges around hole */}
        {holeProgress < 0.3 && (
          <g opacity={1 - holeProgress * 3}>
            {[0, 40, 80, 120, 180, 220, 260, 320].map((angle, i) => (
              <line
                key={i}
                x1={30 + Math.cos((angle * Math.PI) / 180) * 26}
                y1={12 + Math.sin((angle * Math.PI) / 180) * 12}
                x2={30 + Math.cos((angle * Math.PI) / 180) * 32}
                y2={12 + Math.sin((angle * Math.PI) / 180) * 16}
                stroke="#8B6914"
                strokeWidth="2"
                strokeLinecap="round"
              />
            ))}
          </g>
        )}

        {/* Darning stitches - woven pattern */}
        <g opacity={holeProgress}>
          {/* Vertical warp threads */}
          {[-20, -12, -4, 4, 12, 20].map((x, i) => (
            <line
              key={`v${i}`}
              x1={30 + x}
              y1={-2}
              x2={30 + x}
              y2={26}
              stroke={COLORS.RIGHT_ACCENT}
              strokeWidth="2.5"
              strokeLinecap="round"
              opacity={interpolate(holeProgress, [i * 0.1, i * 0.1 + 0.15], [0, 1], {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              })}
            />
          ))}
          {/* Horizontal weft threads */}
          {[-8, -2, 4, 10, 16, 22].map((y, i) => (
            <path
              key={`h${i}`}
              d={`M 5 ${y} Q 20 ${y + (i % 2 === 0 ? -2 : 2)} 30 ${y} Q 40 ${y + (i % 2 === 0 ? 2 : -2)} 55 ${y}`}
              stroke="#E8A848"
              strokeWidth="2"
              fill="none"
              strokeLinecap="round"
              opacity={interpolate(holeProgress, [0.35 + i * 0.08, 0.45 + i * 0.08], [0, 1], {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              })}
            />
          ))}
        </g>
      </g>

      {/* Subtle knit lines on leg */}
      {[50, 65, 80].map((y) => (
        <line key={y} x1="42" y1={y} x2="68" y2={y} stroke="#8B6914" strokeWidth="1" opacity="0.2" />
      ))}

      {/* Subtle knit lines on foot */}
      {[155, 165, 175].map((y) => (
        <line key={y} x1="90" y1={y} x2="230" y2={y} stroke="#8B6914" strokeWidth="1" opacity="0.15" />
      ))}
    </svg>
  );
};

// Needle with thread - more visible
const NeedleAndThread: React.FC<{ stitchProgress: number }> = ({ stitchProgress }) => {
  const cyclePosition = (stitchProgress * 12) % 1;
  const needleY = interpolate(cyclePosition, [0, 0.5, 1], [0, -20, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const needleRotation = interpolate(cyclePosition, [0, 0.5, 1], [-20, 20, -20], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <g transform={`translate(0, ${needleY}) rotate(${needleRotation}, 0, 0)`}>
      {/* Needle - silver/steel */}
      <ellipse cx="0" cy="-45" rx="4" ry="3" fill="#E8E8E8" /> {/* Eye */}
      <line x1="0" y1="-42" x2="0" y2="0" stroke="#D0D0D0" strokeWidth="3" strokeLinecap="round" />
      <line x1="-1" y1="0" x2="1" y2="5" stroke="#B0B0B0" strokeWidth="2" strokeLinecap="round" /> {/* Point */}

      {/* Thread coming from needle */}
      <path
        d="M 0 -45 C -30 -60 -50 -40 -60 -50 C -70 -60 -80 -30 -90 -40"
        stroke={COLORS.RIGHT_ACCENT}
        strokeWidth="2"
        fill="none"
        strokeLinecap="round"
      />
    </g>
  );
};

// Small sock icon for mended items - side view L-shape
const SmallSockIcon: React.FC = () => (
  <svg width="55" height="40" viewBox="0 0 55 40">
    {/* Side view sock - L shape */}
    <path
      d="M 8 3 L 16 3 L 16 18 C 16 22 18 25 22 27 L 48 27 C 52 27 54 30 53 34 C 52 37 48 39 44 39 L 18 39 C 10 39 6 35 6 30 L 6 25 C 6 22 7 20 8 18 Z"
      fill="#C4956A"
      stroke="#8B6914"
      strokeWidth="1.5"
    />
    {/* Cuff */}
    <rect x="7" y="3" width="10" height="6" fill="#A67B5B" rx="1" />
    {/* Patch mark on sole */}
    <ellipse cx="28" cy="33" rx="8" ry="4" fill={COLORS.RIGHT_ACCENT} opacity="0.8" />
  </svg>
);

// Small shirt icon
const SmallShirtIcon: React.FC = () => (
  <svg width="55" height="55" viewBox="0 0 55 55">
    <path
      d="M 12 12 L 20 6 L 27 12 L 34 6 L 42 12 L 38 22 L 38 48 L 16 48 L 16 22 Z"
      fill="#7B8B6F"
      stroke="#5C6B50"
      strokeWidth="1.5"
    />
    {/* Collar */}
    <path d="M 20 6 L 27 14 L 34 6" fill="none" stroke="#5C6B50" strokeWidth="1.5" />
    {/* Elbow patch */}
    <ellipse cx="40" cy="34" rx="5" ry="7" fill={COLORS.RIGHT_ACCENT} opacity="0.8" />
  </svg>
);

// Small trouser icon
const SmallTrouserIcon: React.FC = () => (
  <svg width="50" height="60" viewBox="0 0 50 60">
    <path
      d="M 12 6 L 38 6 L 38 22 L 32 55 L 26 55 L 25 28 L 24 55 L 18 55 L 12 22 Z"
      fill="#5C5C8A"
      stroke="#4A4A70"
      strokeWidth="1.5"
    />
    {/* Waistband */}
    <rect x="12" y="6" width="26" height="5" fill="#4A4A70" />
    {/* Knee patch */}
    <ellipse cx="19" cy="35" rx="5" ry="6" fill={COLORS.RIGHT_ACCENT} opacity="0.8" />
  </svg>
);

const MendedItemIcon: React.FC<{ type: string }> = ({ type }) => {
  if (type === "sock") return <SmallSockIcon />;
  if (type === "shirt") return <SmallShirtIcon />;
  return <SmallTrouserIcon />;
};

export const RightPanel: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  const syncStart = secondsToFrames(BEATS.SYNC_COMPLETION_START);
  const syncEnd = secondsToFrames(BEATS.SYNC_COMPLETION_END);
  const satisfactionStart = secondsToFrames(BEATS.SATISFACTION_START);
  const satisfactionEnd = secondsToFrames(BEATS.SATISFACTION_END);
  const zoomStart = secondsToFrames(BEATS.ZOOM_OUT_START);
  const zoomEnd = secondsToFrames(BEATS.ZOOM_OUT_END);

  // Darning progress (0:08 - 0:15)
  const darningProgress = interpolate(frame, [syncStart, syncEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Scissors snip (at 0:15)
  const scissorsProgress = interpolate(frame, [syncEnd, syncEnd + fps * 0.5], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Sock inspection (0:15 - 0:18)
  const inspectProgress = interpolate(frame, [satisfactionStart, satisfactionEnd], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Zoom out (0:18 - 0:32) with three-phase easing
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

  const scale = interpolate(zoomProgress, [0, 1], [1, 0.35]);
  const translateY = interpolate(zoomProgress, [0, 1], [0, -80]);

  const mendedItemsOpacity = interpolate(zoomProgress, [0.3, 0.6], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const sockLift = interpolate(inspectProgress, [0, 0.5, 1], [0, -40, 0]);
  const sockRotate = interpolate(inspectProgress, [0, 0.5, 1], [0, -15, 0]);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.RIGHT_BG,
        overflow: "hidden",
      }}
    >
      {/* Warm ambient light gradient */}
      <div
        style={{
          position: "absolute",
          top: 0,
          right: 0,
          width: "70%",
          height: "70%",
          background: `radial-gradient(ellipse at 75% 15%, ${COLORS.RIGHT_ACCENT}40 0%, transparent 55%)`,
          pointerEvents: "none",
        }}
      />

      {/* Main darning scene */}
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: "50%",
          transform: `translate(-50%, -50%) scale(${scale}) translateY(${translateY}px)`,
          transformOrigin: "center center",
        }}
      >
        {/* Wooden table surface */}
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
          {/* Oil lamp in corner */}
          <div style={{ position: "absolute", top: -80, right: 20 }}>
            <svg width="70" height="120" viewBox="0 0 70 120">
              {/* Lamp base */}
              <ellipse cx="35" cy="105" rx="28" ry="10" fill="#8B4513" />
              <path d="M 15 105 L 20 55 L 50 55 L 55 105" fill="#CD853F" stroke="#8B4513" strokeWidth="2" />
              {/* Oil reservoir */}
              <ellipse cx="35" cy="55" rx="18" ry="8" fill="#B8860B" />
              {/* Glass chimney */}
              <path
                d="M 22 55 C 20 45 18 35 18 20 C 18 8 52 8 52 20 C 52 35 50 45 48 55"
                fill="rgba(255,220,150,0.15)"
                stroke="rgba(255,255,255,0.25)"
                strokeWidth="1"
              />
              {/* Flame glow */}
              <ellipse cx="35" cy="35" rx="10" ry="18" fill="#FFD700" opacity="0.9">
                <animate attributeName="ry" values="18;20;18" dur="0.5s" repeatCount="indefinite" />
              </ellipse>
              <ellipse cx="35" cy="33" rx="6" ry="12" fill="#FFA500" />
              <ellipse cx="35" cy="30" rx="3" ry="8" fill="#FF6B35" />
            </svg>
            {/* Glow effect */}
            <div
              style={{
                position: "absolute",
                top: 0,
                left: -30,
                width: 130,
                height: 130,
                background: `radial-gradient(circle, ${COLORS.RIGHT_ACCENT}55 0%, transparent 65%)`,
                pointerEvents: "none",
              }}
            />
          </div>

          {/* Hands holding the sock (simplified) */}
          <div
            style={{
              position: "absolute",
              left: "50%",
              top: "45%",
              transform: `translate(-50%, -50%) translateY(${sockLift}px) rotate(${sockRotate}deg)`,
            }}
          >
            {/* Left hand silhouette */}
            <svg
              style={{ position: "absolute", left: -60, top: 80 }}
              width="80"
              height="100"
              viewBox="0 0 80 100"
              fill="#8B7355"
              opacity="0.7"
            >
              <ellipse cx="40" cy="50" rx="30" ry="40" />
              <ellipse cx="15" cy="20" rx="8" ry="20" /> {/* Thumb */}
            </svg>

            {/* The sock being darned */}
            <div style={{ position: "relative", zIndex: 2 }}>
              <WoolSock holeProgress={darningProgress} scale={1.2} />
            </div>

            {/* Right hand with needle (during darning) */}
            {darningProgress > 0 && darningProgress < 1 && (
              <svg
                style={{ position: "absolute", right: -20, top: 120, zIndex: 3 }}
                width="100"
                height="120"
                viewBox="-50 -80 100 120"
              >
                {/* Hand silhouette */}
                <ellipse cx="20" cy="20" rx="25" ry="35" fill="#8B7355" opacity="0.7" />
                <NeedleAndThread stitchProgress={darningProgress} />
              </svg>
            )}

            {/* Scissors (appear at completion) */}
            {scissorsProgress > 0 && (
              <div
                style={{
                  position: "absolute",
                  right: -50,
                  top: 100,
                  opacity: scissorsProgress,
                  transform: `rotate(${interpolate(scissorsProgress, [0, 0.3, 1], [0, -30, 0])}deg)`,
                }}
              >
                <svg width="60" height="40" viewBox="0 0 60 40">
                  {/* Scissor blades */}
                  <path d="M 8 18 L 35 12 L 35 10 L 8 14 Z" fill="#C0C0C0" stroke="#909090" strokeWidth="1" />
                  <path d="M 8 22 L 35 28 L 35 30 L 8 26 Z" fill="#C0C0C0" stroke="#909090" strokeWidth="1" />
                  {/* Finger holes */}
                  <ellipse cx="10" cy="14" rx="7" ry="6" fill="none" stroke="#808080" strokeWidth="2" />
                  <ellipse cx="10" cy="26" rx="7" ry="6" fill="none" stroke="#808080" strokeWidth="2" />
                  {/* Pivot */}
                  <circle cx="30" cy="20" r="3" fill="#606060" />
                </svg>
              </div>
            )}
          </div>

          {/* Thread spool on table */}
          <div style={{ position: "absolute", bottom: 30, left: 40 }}>
            <svg width="50" height="50" viewBox="0 0 50 50">
              <ellipse cx="25" cy="40" rx="20" ry="8" fill="#3D2817" />
              <rect x="8" y="15" width="34" height="25" fill={COLORS.RIGHT_ACCENT} />
              <ellipse cx="25" cy="15" rx="17" ry="7" fill="#E8A848" />
              <ellipse cx="25" cy="40" rx="17" ry="7" fill="#B87A28" />
              {/* Thread coming off spool */}
              <path d="M 42 25 Q 55 20 60 30" stroke={COLORS.RIGHT_ACCENT} strokeWidth="2" fill="none" />
            </svg>
          </div>

          {/* Success indicator */}
          {inspectProgress > 0.4 && (
            <div
              style={{
                position: "absolute",
                top: 10,
                left: "50%",
                transform: "translateX(-50%)",
                opacity: interpolate(inspectProgress, [0.4, 0.7], [0, 1], {
                  extrapolateLeft: "clamp",
                  extrapolateRight: "clamp",
                }),
                fontSize: 22,
                color: COLORS.RIGHT_ACCENT,
                fontFamily: "Georgia, serif",
                textShadow: "0 2px 4px rgba(0,0,0,0.5)",
              }}
            >
              ✓ Mended
            </div>
          )}
        </div>
      </div>

      {/* Mended items collection (zoom out) */}
      {mendedItemsOpacity > 0 &&
        MENDED_ITEMS.map((item, i) => (
          <div
            key={i}
            style={{
              position: "absolute",
              left: `${item.x}%`,
              top: `${item.y}%`,
              opacity: mendedItemsOpacity * interpolate(zoomProgress, [0.3 + i * 0.05, 0.45 + i * 0.05], [0, 1], {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              }),
              transform: `rotate(${item.rotation}deg)`,
            }}
          >
            <MendedItemIcon type={item.type} />
          </div>
        ))}

      {/* Wicker basket (late zoom) */}
      {zoomProgress > 0.5 && (
        <div
          style={{
            position: "absolute",
            bottom: 25,
            right: 25,
            opacity: interpolate(zoomProgress, [0.5, 0.85], [0, 0.8], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }),
          }}
        >
          <svg width="110" height="80" viewBox="0 0 110 80">
            {/* Basket body */}
            <path d="M 10 25 C 10 10 100 10 100 25 L 95 70 C 95 78 15 78 15 70 Z" fill="#6B5344" stroke="#4A3828" strokeWidth="2" />
            {/* Weave pattern */}
            {[0, 12, 24, 36, 48].map((y) => (
              <path key={y} d={`M 15 ${28 + y} Q 55 ${33 + y} 95 ${28 + y}`} fill="none" stroke="#4A3828" strokeWidth="1.5" />
            ))}
            {/* Handle */}
            <path d="M 35 25 Q 55 -5 75 25" fill="none" stroke="#5C4A36" strokeWidth="4" />
          </svg>
        </div>
      )}

      {/* Grandmother silhouette */}
      {zoomProgress > 0.5 && (
        <div
          style={{
            position: "absolute",
            bottom: 35,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: interpolate(zoomProgress, [0.5, 0.8], [0, 0.6], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }),
          }}
        >
          <svg width="55" height="70" viewBox="0 0 55 70" fill={COLORS.RIGHT_ACCENT}>
            <circle cx="27" cy="12" r="11" />
            <ellipse cx="27" cy="5" rx="7" ry="5" /> {/* Hair bun */}
            <path d="M 15 23 C 8 25 5 40 8 65 L 46 65 C 49 40 46 25 39 23 C 35 22 30 25 27 25 C 24 25 19 22 15 23 Z" />
          </svg>
        </div>
      )}
    </AbsoluteFill>
  );
};
