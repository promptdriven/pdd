import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  UI_FONT,
  STAGE_LABEL_SIZE,
} from "./constants";

export type StageIconType =
  | "document_code"
  | "document_text"
  | "gear"
  | "neural_network"
  | "gate_cluster"
  | "code_brackets"
  | "shield_check";

interface FlowStageIconProps {
  x: number;
  y: number;
  iconType: StageIconType;
  color: string;
  opacity: number;
  label: string;
  fadeStart: number;
  fadeDuration: number;
}

const DocumentCodeIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width={70} height={90} viewBox="0 0 70 90">
    <rect
      x={5}
      y={5}
      width={60}
      height={80}
      rx={4}
      fill="none"
      stroke={color}
      strokeWidth={2}
    />
    {/* Code lines */}
    <line x1={16} y1={28} x2={40} y2={28} stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1={20} y1={38} x2={50} y2={38} stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1={20} y1={48} x2={44} y2={48} stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1={16} y1={58} x2={36} y2={58} stroke={color} strokeWidth={1.5} opacity={0.6} />
    {/* Fold corner */}
    <path d="M 50 5 L 65 5 L 65 20 Z" fill="none" stroke={color} strokeWidth={1.5} opacity={0.4} />
  </svg>
);

const DocumentTextIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width={70} height={90} viewBox="0 0 70 90">
    <rect
      x={5}
      y={5}
      width={60}
      height={80}
      rx={4}
      fill="none"
      stroke={color}
      strokeWidth={2}
    />
    {/* Text lines */}
    <line x1={16} y1={28} x2={54} y2={28} stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1={16} y1={38} x2={48} y2={38} stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1={16} y1={48} x2={52} y2={48} stroke={color} strokeWidth={1.5} opacity={0.6} />
    <line x1={16} y1={58} x2={40} y2={58} stroke={color} strokeWidth={1.5} opacity={0.6} />
    {/* Fold corner */}
    <path d="M 50 5 L 65 5 L 65 20 Z" fill="none" stroke={color} strokeWidth={1.5} opacity={0.4} />
  </svg>
);

const GearIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width={60} height={60} viewBox="0 0 60 60">
    <path
      d={`
        M 26 4 L 34 4 L 36 10 L 38 11 L 44 7 L 50 13 L 46 19 L 47 21 L 53 23
        L 53 31 L 47 33 L 46 35 L 50 41 L 44 47 L 38 43 L 36 44 L 34 50
        L 26 50 L 24 44 L 22 43 L 16 47 L 10 41 L 14 35 L 13 33 L 7 31
        L 7 23 L 13 21 L 14 19 L 10 13 L 16 7 L 22 11 L 24 10 Z
      `}
      fill="none"
      stroke={color}
      strokeWidth={1.5}
      strokeLinejoin="round"
    />
    <circle cx={30} cy={27} r={8} fill="none" stroke={color} strokeWidth={1.5} />
  </svg>
);

const NeuralNetworkIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width={60} height={60} viewBox="0 0 60 60">
    {/* Input layer */}
    <circle cx={10} cy={15} r={4} fill="none" stroke={color} strokeWidth={1.5} />
    <circle cx={10} cy={30} r={4} fill="none" stroke={color} strokeWidth={1.5} />
    <circle cx={10} cy={45} r={4} fill="none" stroke={color} strokeWidth={1.5} />
    {/* Hidden layer */}
    <circle cx={30} cy={12} r={4} fill="none" stroke={color} strokeWidth={1.5} />
    <circle cx={30} cy={27} r={4} fill="none" stroke={color} strokeWidth={1.5} />
    <circle cx={30} cy={42} r={4} fill="none" stroke={color} strokeWidth={1.5} />
    <circle cx={30} cy={52} r={4} fill="none" stroke={color} strokeWidth={1.5} />
    {/* Output layer */}
    <circle cx={50} cy={22} r={4} fill="none" stroke={color} strokeWidth={1.5} />
    <circle cx={50} cy={38} r={4} fill="none" stroke={color} strokeWidth={1.5} />
    {/* Connections — input to hidden */}
    {[15, 30, 45].map((iy) =>
      [12, 27, 42, 52].map((hy) => (
        <line key={`${iy}-${hy}`} x1={14} y1={iy} x2={26} y2={hy} stroke={color} strokeWidth={0.5} opacity={0.4} />
      ))
    )}
    {/* Connections — hidden to output */}
    {[12, 27, 42, 52].map((hy) =>
      [22, 38].map((oy) => (
        <line key={`${hy}-${oy}`} x1={34} y1={hy} x2={46} y2={oy} stroke={color} strokeWidth={0.5} opacity={0.4} />
      ))
    )}
  </svg>
);

const GateClusterIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width={80} height={80} viewBox="0 0 80 80">
    {/* AND gate shapes */}
    <path d="M 10 15 L 10 35 L 25 35 Q 35 35 35 25 Q 35 15 25 15 Z" fill="none" stroke={color} strokeWidth={1.5} />
    <path d="M 45 10 L 45 30 L 60 30 Q 70 30 70 20 Q 70 10 60 10 Z" fill="none" stroke={color} strokeWidth={1.5} />
    <path d="M 25 45 L 25 65 L 40 65 Q 50 65 50 55 Q 50 45 40 45 Z" fill="none" stroke={color} strokeWidth={1.5} />
    {/* Connecting wires */}
    <line x1={35} y1={25} x2={45} y2={20} stroke={color} strokeWidth={1} opacity={0.5} />
    <line x1={35} y1={25} x2={25} y2={55} stroke={color} strokeWidth={1} opacity={0.5} />
    <line x1={70} y1={20} x2={75} y2={20} stroke={color} strokeWidth={1} opacity={0.5} />
    <line x1={50} y1={55} x2={65} y2={55} stroke={color} strokeWidth={1} opacity={0.5} />
  </svg>
);

const CodeBracketsIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width={80} height={80} viewBox="0 0 80 80">
    {/* Left brace */}
    <path
      d="M 30 10 Q 20 10 20 20 L 20 32 Q 20 40 12 40 Q 20 40 20 48 L 20 60 Q 20 70 30 70"
      fill="none"
      stroke={color}
      strokeWidth={2}
    />
    {/* Right brace */}
    <path
      d="M 50 10 Q 60 10 60 20 L 60 32 Q 60 40 68 40 Q 60 40 60 48 L 60 60 Q 60 70 50 70"
      fill="none"
      stroke={color}
      strokeWidth={2}
    />
    {/* Code lines inside */}
    <line x1={34} y1={30} x2={50} y2={30} stroke={color} strokeWidth={1} opacity={0.5} />
    <line x1={34} y1={40} x2={46} y2={40} stroke={color} strokeWidth={1} opacity={0.5} />
    <line x1={34} y1={50} x2={52} y2={50} stroke={color} strokeWidth={1} opacity={0.5} />
  </svg>
);

const ShieldCheckIcon: React.FC<{ color: string }> = ({ color }) => (
  <svg width={50} height={60} viewBox="0 0 50 60">
    {/* Shield outline */}
    <path
      d="M 25 5 L 45 15 L 45 35 Q 45 50 25 55 Q 5 50 5 35 L 5 15 Z"
      fill="none"
      stroke={color}
      strokeWidth={2}
    />
    {/* Checkmark */}
    <path
      d="M 15 30 L 22 38 L 36 22"
      fill="none"
      stroke={color}
      strokeWidth={2.5}
      strokeLinecap="round"
      strokeLinejoin="round"
    />
  </svg>
);

const ICON_COMPONENTS: Record<StageIconType, React.FC<{ color: string }>> = {
  document_code: DocumentCodeIcon,
  document_text: DocumentTextIcon,
  gear: GearIcon,
  neural_network: NeuralNetworkIcon,
  gate_cluster: GateClusterIcon,
  code_brackets: CodeBracketsIcon,
  shield_check: ShieldCheckIcon,
};

const ICON_SIZES: Record<StageIconType, { w: number; h: number }> = {
  document_code: { w: 70, h: 90 },
  document_text: { w: 70, h: 90 },
  gear: { w: 60, h: 60 },
  neural_network: { w: 60, h: 60 },
  gate_cluster: { w: 80, h: 80 },
  code_brackets: { w: 80, h: 80 },
  shield_check: { w: 50, h: 60 },
};

export const FlowStageIcon: React.FC<FlowStageIconProps> = ({
  x,
  y,
  iconType,
  color,
  opacity: targetOpacity,
  label,
  fadeStart,
  fadeDuration,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [fadeStart, fadeStart + fadeDuration],
    [0, targetOpacity],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  if (frame < fadeStart) return null;

  const IconComponent = ICON_COMPONENTS[iconType];
  const size = ICON_SIZES[iconType];

  return (
    <>
      <div
        style={{
          position: "absolute",
          left: x - size.w / 2,
          top: y - size.h / 2,
          opacity,
          pointerEvents: "none",
        }}
      >
        <IconComponent color={color} />
      </div>
      <div
        style={{
          position: "absolute",
          left: x - 50,
          top: y + size.h / 2 + 6,
          width: 100,
          textAlign: "center",
          fontFamily: UI_FONT,
          fontSize: STAGE_LABEL_SIZE,
          color,
          opacity,
          pointerEvents: "none",
        }}
      >
        {label}
      </div>
    </>
  );
};

export default FlowStageIcon;
