import React from "react";
import {
  NOZZLE_COLOR,
  WALLS_COLOR,
  CAVITY_COLOR,
  CANVAS_WIDTH,
} from "./constants";

interface MoldCrossSectionProps {
  wallsGlow: number;
  nozzleGlow: number;
  cavityGlow: number;
}

const MoldCrossSection: React.FC<MoldCrossSectionProps> = ({
  wallsGlow,
  nozzleGlow,
  cavityGlow,
}) => {
  const moldWidth = 700;
  const moldHeight = 350;
  const centerX = CANVAS_WIDTH / 2;

  return (
    <div
      style={{
        position: "absolute",
        top: 150,
        left: centerX - moldWidth / 2,
        width: moldWidth,
        height: moldHeight,
        transform: "scale(0.7)",
        transformOrigin: "center top",
      }}
    >
      {/* Nozzle (top center funnel) */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: moldWidth / 2 - 30,
          width: 60,
          height: 80,
          background: `linear-gradient(180deg, ${NOZZLE_COLOR} 0%, ${NOZZLE_COLOR}88 100%)`,
          clipPath: "polygon(30% 0%, 70% 0%, 60% 100%, 40% 100%)",
          boxShadow: `0 0 ${20 + nozzleGlow * 30}px ${NOZZLE_COLOR}`,
          opacity: 0.7 + nozzleGlow,
        }}
      />
      {/* Nozzle glow overlay */}
      <div
        style={{
          position: "absolute",
          top: -10,
          left: moldWidth / 2 - 50,
          width: 100,
          height: 100,
          borderRadius: "50%",
          background: `radial-gradient(circle, ${NOZZLE_COLOR}${Math.round(nozzleGlow * 255)
            .toString(16)
            .padStart(2, "0")} 0%, transparent 70%)`,
          pointerEvents: "none",
        }}
      />

      {/* Left mold wall */}
      <div
        style={{
          position: "absolute",
          top: 60,
          left: 40,
          width: 120,
          height: 260,
          background: `linear-gradient(90deg, ${WALLS_COLOR}CC 0%, ${WALLS_COLOR}66 100%)`,
          borderRadius: "8px 4px 4px 8px",
          boxShadow: `0 0 ${15 + wallsGlow * 40}px ${WALLS_COLOR}`,
          opacity: 0.6 + wallsGlow,
        }}
      />
      {/* Left wall glow */}
      <div
        style={{
          position: "absolute",
          top: 100,
          left: 20,
          width: 160,
          height: 200,
          borderRadius: "50%",
          background: `radial-gradient(ellipse, ${WALLS_COLOR}${Math.round(wallsGlow * 200)
            .toString(16)
            .padStart(2, "0")} 0%, transparent 70%)`,
          pointerEvents: "none",
        }}
      />

      {/* Right mold wall */}
      <div
        style={{
          position: "absolute",
          top: 60,
          right: 40,
          width: 120,
          height: 260,
          background: `linear-gradient(270deg, ${WALLS_COLOR}CC 0%, ${WALLS_COLOR}66 100%)`,
          borderRadius: "4px 8px 8px 4px",
          boxShadow: `0 0 ${15 + wallsGlow * 40}px ${WALLS_COLOR}`,
          opacity: 0.6 + wallsGlow,
        }}
      />
      {/* Right wall glow */}
      <div
        style={{
          position: "absolute",
          top: 100,
          right: 20,
          width: 160,
          height: 200,
          borderRadius: "50%",
          background: `radial-gradient(ellipse, ${WALLS_COLOR}${Math.round(wallsGlow * 200)
            .toString(16)
            .padStart(2, "0")} 0%, transparent 70%)`,
          pointerEvents: "none",
        }}
      />

      {/* Cavity (center space) */}
      <div
        style={{
          position: "absolute",
          top: 80,
          left: 160,
          width: moldWidth - 320,
          height: 220,
          background: `radial-gradient(ellipse, ${CAVITY_COLOR}${Math.round(cavityGlow * 180)
            .toString(16)
            .padStart(2, "0")} 0%, ${CAVITY_COLOR}11 60%, transparent 100%)`,
          borderRadius: 12,
          border: `1px solid ${CAVITY_COLOR}44`,
        }}
      />

      {/* Bottom plate */}
      <div
        style={{
          position: "absolute",
          bottom: 0,
          left: 30,
          width: moldWidth - 60,
          height: 30,
          background: `linear-gradient(0deg, ${WALLS_COLOR}88 0%, ${WALLS_COLOR}44 100%)`,
          borderRadius: "0 0 6px 6px",
          boxShadow: `0 0 ${10 + wallsGlow * 25}px ${WALLS_COLOR}`,
          opacity: 0.5 + wallsGlow * 0.5,
        }}
      />

      {/* Top plate */}
      <div
        style={{
          position: "absolute",
          top: 55,
          left: 30,
          width: moldWidth - 60,
          height: 20,
          background: `linear-gradient(180deg, ${WALLS_COLOR}88 0%, ${WALLS_COLOR}44 100%)`,
          borderRadius: "6px 6px 0 0",
          boxShadow: `0 0 ${10 + wallsGlow * 25}px ${WALLS_COLOR}`,
          opacity: 0.5 + wallsGlow * 0.5,
        }}
      />
    </div>
  );
};

export default MoldCrossSection;
