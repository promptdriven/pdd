import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing, OffthreadVideo, staticFile } from "remotion";
import { COLORS, BEATS, CONTACT_POINTS, MoldFlowFocusPropsType } from "./constants";

interface ContactPoint {
  x: number;
  y: number;
  intensity: number;
}

interface WallGlowProps {
  baseOpacity: number;
  contactPoints: ContactPoint[];
  color: string;
}

const WallGlow: React.FC<WallGlowProps> = ({ baseOpacity, contactPoints, color }) => {
  return (
    <>
      {/* Base wall outline glow */}
      <svg
        style={{
          position: "absolute",
          width: "100%",
          height: "100%",
          pointerEvents: "none",
        }}
      >
        {/* Glow filter definition */}
        <defs>
          <filter id="wallGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation="8" result="coloredBlur" />
            <feMerge>
              <feMergeNode in="coloredBlur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
          <filter id="strongGlow" x="-100%" y="-100%" width="300%" height="300%">
            <feGaussianBlur stdDeviation="15" result="coloredBlur" />
            <feMerge>
              <feMergeNode in="coloredBlur" />
              <feMergeNode in="coloredBlur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Left wall */}
        <rect
          x={400}
          y={250}
          width={40}
          height={400}
          fill="none"
          stroke={color}
          strokeWidth={6}
          opacity={baseOpacity}
          filter="url(#wallGlow)"
        />

        {/* Right wall */}
        <rect
          x={1480}
          y={250}
          width={40}
          height={400}
          fill="none"
          stroke={color}
          strokeWidth={6}
          opacity={baseOpacity}
          filter="url(#wallGlow)"
        />

        {/* Bottom wall */}
        <rect
          x={400}
          y={610}
          width={1120}
          height={40}
          fill="none"
          stroke={color}
          strokeWidth={6}
          opacity={baseOpacity}
          filter="url(#wallGlow)"
        />

        {/* Top injection opening frame (left side) */}
        <rect
          x={400}
          y={200}
          width={400}
          height={50}
          fill="none"
          stroke={color}
          strokeWidth={4}
          opacity={baseOpacity * 0.7}
          filter="url(#wallGlow)"
        />

        {/* Top injection opening frame (right side) */}
        <rect
          x={1120}
          y={200}
          width={400}
          height={50}
          fill="none"
          stroke={color}
          strokeWidth={4}
          opacity={baseOpacity * 0.7}
          filter="url(#wallGlow)"
        />
      </svg>

      {/* Contact point pulses */}
      {contactPoints.map(
        (point, i) =>
          point.intensity > 0 && (
            <div
              key={i}
              style={{
                position: "absolute",
                left: point.x - 60,
                top: point.y - 60,
                width: 120,
                height: 120,
                borderRadius: "50%",
                background: `radial-gradient(circle, ${color}${Math.floor(point.intensity * 200)
                  .toString(16)
                  .padStart(2, "0")} 0%, transparent 70%)`,
                pointerEvents: "none",
              }}
            />
          )
      )}
    </>
  );
};

interface LiquidFlowProps {
  progress: number;
  color: string;
}

const LiquidFlow: React.FC<LiquidFlowProps> = ({ progress, color }) => {
  // Liquid flows down from injection point and spreads
  const flowY = interpolate(progress, [0, 0.4], [200, 550], {
    extrapolateRight: "clamp",
  });
  const spreadX = interpolate(progress, [0.2, 0.8], [0, 400], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <svg
      style={{
        position: "absolute",
        width: "100%",
        height: "100%",
        pointerEvents: "none",
      }}
    >
      <defs>
        <filter id="liquidGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="4" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Main liquid blob */}
      <ellipse
        cx={960}
        cy={flowY}
        rx={80 + spreadX}
        ry={60 + progress * 80}
        fill={color}
        opacity={0.6}
        filter="url(#liquidGlow)"
      />

      {/* Chaotic flow particles */}
      {progress > 0.1 &&
        [0, 1, 2, 3, 4].map((i) => {
          const offsetX = Math.sin(progress * 10 + i * 2) * (50 + i * 20);
          const offsetY = Math.cos(progress * 8 + i * 1.5) * 30;
          const particleProgress = Math.min(1, progress + i * 0.05);
          return (
            <circle
              key={i}
              cx={960 + offsetX}
              cy={Math.min(flowY + offsetY, 580)}
              r={15 - i * 2}
              fill={color}
              opacity={0.4 * (1 - particleProgress * 0.5)}
              filter="url(#liquidGlow)"
            />
          );
        })}

      {/* Side spreading when hitting walls */}
      {progress > 0.5 && (
        <>
          <ellipse
            cx={500 + (progress - 0.5) * 200}
            cy={550}
            rx={40 + (progress - 0.5) * 100}
            ry={30}
            fill={color}
            opacity={0.5 * Math.min(1, (progress - 0.5) * 2)}
            filter="url(#liquidGlow)"
          />
          <ellipse
            cx={1420 - (progress - 0.5) * 200}
            cy={550}
            rx={40 + (progress - 0.5) * 100}
            ry={30}
            fill={color}
            opacity={0.5 * Math.min(1, (progress - 0.5) * 2)}
            filter="url(#liquidGlow)"
          />
        </>
      )}
    </svg>
  );
};

export const MoldFlowFocus: React.FC<MoldFlowFocusPropsType> = ({
  showLabel = true,
}) => {
  const frame = useCurrentFrame();

  // Base wall glow (0-3s)
  const wallGlow = interpolate(
    frame,
    [BEATS.WALL_GLOW_START, BEATS.WALL_GLOW_END],
    [0, 0.6],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Liquid flow progress
  const flowProgress = interpolate(
    frame,
    [BEATS.WALL_GLOW_END, BEATS.CONSTRAIN_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
  );

  // Contact pulse effects (multiple contact points)
  const contactPulse1 =
    frame > BEATS.CONTACT_1_START
      ? Math.sin((frame - BEATS.CONTACT_1_START) * 0.15) * 0.3 + 0.7
      : 0;
  const contactPulse2 =
    frame > BEATS.CONTACT_2_START
      ? Math.sin((frame - BEATS.CONTACT_2_START) * 0.15) * 0.3 + 0.7
      : 0;
  const contactPulse3 =
    frame > BEATS.CONTACT_3_START
      ? Math.sin((frame - BEATS.CONTACT_3_START) * 0.15) * 0.3 + 0.7
      : 0;

  // Wall glow intensifies at contact
  const wallGlowIntensified = interpolate(
    frame,
    [BEATS.CONTACT_1_START, BEATS.CONTACT_1_START + 30],
    [wallGlow, Math.min(1, wallGlow + 0.3)],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Label opacity (10-12s)
  const labelOpacity = interpolate(
    frame,
    [BEATS.LABEL_START, BEATS.LABEL_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Contact points with calculated intensities
  const contactPoints: ContactPoint[] = [
    { x: CONTACT_POINTS[0].x + 150, y: CONTACT_POINTS[0].y, intensity: contactPulse1 },
    { x: CONTACT_POINTS[1].x + 550, y: CONTACT_POINTS[1].y, intensity: contactPulse2 },
    { x: CONTACT_POINTS[2].x + 350, y: CONTACT_POINTS[2].y + 50, intensity: contactPulse3 },
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Veo video background */}
      <OffthreadVideo
        src={staticFile("veo_mold_flow_focus.mp4")}
        style={{ width: "100%", height: "100%", objectFit: "cover" }}
      />

      {/* Liquid flow animation */}
      <LiquidFlow progress={flowProgress} color={COLORS.LIQUID_BLUE} />

      {/* Wall glow overlay */}
      <WallGlow
        baseOpacity={wallGlowIntensified}
        contactPoints={contactPoints}
        color={COLORS.WALLS_AMBER}
      />

      {/* Bottom label */}
      {showLabel && labelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 100,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: labelOpacity,
          }}
        >
          <div
            style={{
              fontSize: 36,
              fontWeight: "bold",
              color: COLORS.WALLS_AMBER,
              fontFamily: "sans-serif",
              textShadow: `0 0 20px ${COLORS.WALLS_AMBER}`,
            }}
          >
            Walls do the precision work
          </div>
          <div
            style={{
              fontSize: 20,
              color: COLORS.LABEL_GRAY,
              fontFamily: "sans-serif",
              marginTop: 12,
            }}
          >
            The material flows freely until constrained
          </div>
        </div>
      )}

      {/* Title */}
      <div
        style={{
          position: "absolute",
          top: 40,
          left: 0,
          right: 0,
          textAlign: "center",
        }}
      >
        <span
          style={{
            fontSize: 24,
            fontFamily: "sans-serif",
            color: COLORS.LABEL_WHITE,
            opacity: 0.8,
          }}
        >
          Injection Mold Cross-Section
        </span>
      </div>
    </AbsoluteFill>
  );
};
