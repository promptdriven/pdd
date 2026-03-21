import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
} from "remotion";

export const Part3MoldTitleCard: React.FC = () => {
  const frame = useCurrentFrame();
  const { durationInFrames } = useVideoConfig();

  // === Background fade-in: frames 0-15 ===
  const bgOpacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // === Blueprint grid opacity: frames 0-15 ===
  const gridOpacity = interpolate(frame, [0, 15], [0, 0.05], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // === "PART 3" label: fades in frames 15-35 ===
  const partLabelOpacity = interpolate(frame, [15, 35], [0, 0.5], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // === "THE MOLD HAS" typewriter: frames 40-76 (12 chars × 3 frames each) ===
  const moldHasText = "THE MOLD HAS";
  const charsVisible = Math.min(
    moldHasText.length,
    Math.max(0, Math.floor((frame - 40) / 3))
  );
  const moldHasDisplay = moldHasText.substring(0, charsVisible);

  // === Horizontal rule: draws from center outward, frames 60-70 ===
  const ruleProgress = interpolate(frame, [60, 70], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
    easing: Easing.inOut(Easing.quad),
  });
  const ruleWidth = ruleProgress * 200; // 200px total width

  // === "THREE PARTS" fade-in + slide-up: frames 70-90 ===
  const threePartsOpacity = interpolate(frame, [70, 90], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
    easing: Easing.out(Easing.quad),
  });
  const threePartsSlide = interpolate(frame, [70, 90], [10, 0], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // === Ghost shapes: stroke-draw frames 15-75, pulse frames 90+ ===
  const ghostDrawProgress = interpolate(frame, [15, 75], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });
  const ghostBaseOpacity = 0.04 * ghostDrawProgress;

  // Ghost pulse during hold phase (frames 90-120), 30-frame cycle
  const ghostPulse =
    frame >= 90
      ? interpolate(
          Math.sin(((frame - 90) / 30) * Math.PI * 2),
          [-1, 1],
          [0.03, 0.05],
          { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
        )
      : ghostBaseOpacity;

  const ghostOpacity = frame >= 90 ? ghostPulse : ghostBaseOpacity;

  // === Glow opacity ===
  const glowOpacity = 0.02 * ghostDrawProgress;

  // Blueprint grid pattern (60px spacing)
  const renderBlueprintGrid = () => {
    const lines: React.ReactElement[] = [];
    // Vertical lines
    for (let x = 0; x <= 1920; x += 60) {
      lines.push(
        <line
          key={`v-${x}`}
          x1={x}
          y1={0}
          x2={x}
          y2={1080}
          stroke="#1E293B"
          strokeWidth={1}
        />
      );
    }
    // Horizontal lines
    for (let y = 0; y <= 1080; y += 60) {
      lines.push(
        <line
          key={`h-${y}`}
          x1={0}
          y1={y}
          x2={1920}
          y2={y}
          stroke="#1E293B"
          strokeWidth={1}
        />
      );
    }
    return (
      <svg
        width={1920}
        height={1080}
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          opacity: gridOpacity,
        }}
      >
        {lines}
      </svg>
    );
  };

  // Ghost shape: Wall segment (left)
  const renderWallSegment = () => {
    const dashLen = 200;
    const dashOffset = (1 - ghostDrawProgress) * dashLen;
    return (
      <div
        style={{
          position: "absolute",
          left: 560 - 50,
          top: 480 - 40,
          width: 100,
          height: 80,
        }}
      >
        <svg width={100} height={80} style={{ position: "absolute" }}>
          {/* Glow */}
          <rect
            x={10}
            y={10}
            width={80}
            height={60}
            fill="none"
            stroke="#D9944A"
            strokeWidth={2}
            opacity={glowOpacity}
            filter="url(#glowAmber)"
          />
          {/* Main shape */}
          <rect
            x={10}
            y={10}
            width={80}
            height={60}
            fill="none"
            stroke="#D9944A"
            strokeWidth={2}
            opacity={ghostOpacity}
            strokeDasharray={dashLen}
            strokeDashoffset={dashOffset}
          />
          {/* Inner block */}
          <rect
            x={25}
            y={25}
            width={50}
            height={30}
            fill="none"
            stroke="#D9944A"
            strokeWidth={1.5}
            opacity={ghostOpacity * 0.8}
            strokeDasharray={dashLen}
            strokeDashoffset={dashOffset}
          />
          <defs>
            <filter id="glowAmber" x="-50%" y="-50%" width="200%" height="200%">
              <feGaussianBlur stdDeviation={8} />
            </filter>
          </defs>
        </svg>
        {/* Label */}
        <div
          style={{
            position: "absolute",
            top: 85,
            width: "100%",
            textAlign: "center",
            fontFamily: "'Inter', sans-serif",
            fontSize: 8,
            color: "#D9944A",
            opacity: 0.03 * ghostDrawProgress,
          }}
        >
          WALLS
        </div>
      </div>
    );
  };

  // Ghost shape: Injection nozzle (center)
  const renderNozzle = () => {
    const dashLen = 300;
    const dashOffset = (1 - ghostDrawProgress) * dashLen;
    return (
      <div
        style={{
          position: "absolute",
          left: 960 - 40,
          top: 430 - 50,
          width: 80,
          height: 100,
        }}
      >
        <svg width={80} height={100} style={{ position: "absolute" }}>
          {/* Glow */}
          <polygon
            points="20,10 60,10 70,90 10,90"
            fill="none"
            stroke="#4A90D9"
            strokeWidth={2}
            opacity={glowOpacity}
            filter="url(#glowBlue)"
          />
          {/* Main shape - tapered funnel */}
          <polygon
            points="20,10 60,10 70,90 10,90"
            fill="none"
            stroke="#4A90D9"
            strokeWidth={2}
            opacity={ghostOpacity}
            strokeDasharray={dashLen}
            strokeDashoffset={dashOffset}
          />
          <defs>
            <filter id="glowBlue" x="-50%" y="-50%" width="200%" height="200%">
              <feGaussianBlur stdDeviation={8} />
            </filter>
          </defs>
        </svg>
        {/* Label */}
        <div
          style={{
            position: "absolute",
            top: 105,
            width: "100%",
            textAlign: "center",
            fontFamily: "'Inter', sans-serif",
            fontSize: 8,
            color: "#4A90D9",
            opacity: 0.03 * ghostDrawProgress,
          }}
        >
          NOZZLE
        </div>
      </div>
    );
  };

  // Ghost shape: Material swatch (right)
  const renderMaterialSwatch = () => {
    const dashLen = 300;
    const dashOffset = (1 - ghostDrawProgress) * dashLen;
    return (
      <div
        style={{
          position: "absolute",
          left: 1360 - 50,
          top: 480 - 40,
          width: 100,
          height: 80,
        }}
      >
        <svg width={100} height={80} style={{ position: "absolute" }}>
          {/* Glow */}
          <path
            d="M10,40 Q25,10 50,15 Q75,20 90,40 Q75,65 50,70 Q25,65 10,40 Z"
            fill="none"
            stroke="#5AAA6E"
            strokeWidth={2}
            opacity={glowOpacity}
            filter="url(#glowGreen)"
          />
          {/* Main shape - organic flowing texture */}
          <path
            d="M10,40 Q25,10 50,15 Q75,20 90,40 Q75,65 50,70 Q25,65 10,40 Z"
            fill="none"
            stroke="#5AAA6E"
            strokeWidth={2}
            opacity={ghostOpacity}
            strokeDasharray={dashLen}
            strokeDashoffset={dashOffset}
          />
          <defs>
            <filter id="glowGreen" x="-50%" y="-50%" width="200%" height="200%">
              <feGaussianBlur stdDeviation={8} />
            </filter>
          </defs>
        </svg>
        {/* Label */}
        <div
          style={{
            position: "absolute",
            top: 85,
            width: "100%",
            textAlign: "center",
            fontFamily: "'Inter', sans-serif",
            fontSize: 8,
            color: "#5AAA6E",
            opacity: 0.03 * ghostDrawProgress,
          }}
        >
          MATERIAL
        </div>
      </div>
    );
  };

  return (
    <AbsoluteFill style={{ backgroundColor: "#000000" }}>
      {/* Main background */}
      <AbsoluteFill
        style={{
          backgroundColor: "#0A0F1A",
          opacity: bgOpacity,
        }}
      >
        {/* Blueprint grid */}
        {renderBlueprintGrid()}

        {/* Ghost shapes */}
        {renderWallSegment()}
        {renderNozzle()}
        {renderMaterialSwatch()}

        {/* "PART 3" section label */}
        <div
          style={{
            position: "absolute",
            top: 400,
            width: "100%",
            textAlign: "center",
            fontFamily: "'Inter', sans-serif",
            fontWeight: 600,
            fontSize: 14,
            color: "#64748B",
            opacity: partLabelOpacity,
            letterSpacing: 4,
          }}
        >
          PART 3
        </div>

        {/* "THE MOLD HAS" — typewriter */}
        <div
          style={{
            position: "absolute",
            top: 460,
            width: "100%",
            textAlign: "center",
            fontFamily: "'Inter', sans-serif",
            fontWeight: 700,
            fontSize: 72,
            color: "#E2E8F0",
            whiteSpace: "pre",
          }}
        >
          {moldHasDisplay}
        </div>

        {/* Horizontal rule — draws from center outward */}
        {frame >= 60 && (
          <div
            style={{
              position: "absolute",
              top: 505,
              left: 960 - ruleWidth / 2,
              width: ruleWidth,
              height: 2,
              backgroundColor: "#334155",
              opacity: 0.5,
            }}
          />
        )}

        {/* "THREE PARTS" — fade-in + slide-up, 15px offset-right (x:975) */}
        <div
          style={{
            position: "absolute",
            top: 545 + threePartsSlide,
            width: "100%",
            textAlign: "center",
            fontFamily: "'Inter', sans-serif",
            fontWeight: 700,
            fontSize: 72,
            color: "#E2E8F0",
            opacity: threePartsOpacity,
            paddingLeft: 30,
          }}
        >
          THREE PARTS
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3MoldTitleCard;
