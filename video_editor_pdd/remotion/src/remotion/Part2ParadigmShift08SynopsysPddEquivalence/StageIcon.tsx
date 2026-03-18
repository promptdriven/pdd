import React from 'react';

type IconType =
  | 'document_code'
  | 'gear'
  | 'gate_cluster'
  | 'shield_check'
  | 'document_text'
  | 'neural_network'
  | 'code_brackets';

interface StageIconProps {
  icon: IconType;
  color: string;
  opacity: number;
}

const DocumentCode: React.FC<{ color: string; opacity: number }> = ({ color, opacity }) => (
  <svg width={70} height={90} viewBox="0 0 70 90">
    <rect
      x={2} y={2} width={66} height={86} rx={4}
      fill="none" stroke={color} strokeWidth={2} opacity={opacity}
    />
    {/* Code lines */}
    <line x1={14} y1={22} x2={40} y2={22} stroke={color} strokeWidth={1.5} opacity={opacity * 0.7} />
    <line x1={20} y1={34} x2={50} y2={34} stroke={color} strokeWidth={1.5} opacity={opacity * 0.7} />
    <line x1={20} y1={46} x2={44} y2={46} stroke={color} strokeWidth={1.5} opacity={opacity * 0.7} />
    <line x1={14} y1={58} x2={36} y2={58} stroke={color} strokeWidth={1.5} opacity={opacity * 0.7} />
    <line x1={20} y1={70} x2={52} y2={70} stroke={color} strokeWidth={1.5} opacity={opacity * 0.7} />
  </svg>
);

const DocumentText: React.FC<{ color: string; opacity: number }> = ({ color, opacity }) => (
  <svg width={70} height={90} viewBox="0 0 70 90">
    <rect
      x={2} y={2} width={66} height={86} rx={4}
      fill="none" stroke={color} strokeWidth={2} opacity={opacity}
    />
    {/* Text lines */}
    <line x1={14} y1={22} x2={56} y2={22} stroke={color} strokeWidth={1.5} opacity={opacity * 0.7} />
    <line x1={14} y1={34} x2={48} y2={34} stroke={color} strokeWidth={1.5} opacity={opacity * 0.7} />
    <line x1={14} y1={46} x2={52} y2={46} stroke={color} strokeWidth={1.5} opacity={opacity * 0.7} />
    <line x1={14} y1={58} x2={42} y2={58} stroke={color} strokeWidth={1.5} opacity={opacity * 0.7} />
    <line x1={14} y1={70} x2={50} y2={70} stroke={color} strokeWidth={1.5} opacity={opacity * 0.7} />
  </svg>
);

const Gear: React.FC<{ color: string; opacity: number }> = ({ color, opacity }) => (
  <svg width={60} height={60} viewBox="0 0 60 60">
    <circle cx={30} cy={30} r={10} fill="none" stroke={color} strokeWidth={2} opacity={opacity} />
    <circle cx={30} cy={30} r={22} fill="none" stroke={color} strokeWidth={2} opacity={opacity} strokeDasharray="6 4" />
    {/* Gear teeth */}
    {[0, 45, 90, 135, 180, 225, 270, 315].map((angle) => {
      const rad = (angle * Math.PI) / 180;
      const x1 = 30 + 20 * Math.cos(rad);
      const y1 = 30 + 20 * Math.sin(rad);
      const x2 = 30 + 27 * Math.cos(rad);
      const y2 = 30 + 27 * Math.sin(rad);
      return (
        <line
          key={angle}
          x1={x1} y1={y1} x2={x2} y2={y2}
          stroke={color} strokeWidth={3} strokeLinecap="round" opacity={opacity}
        />
      );
    })}
  </svg>
);

const GateCluster: React.FC<{ color: string; opacity: number }> = ({ color, opacity }) => (
  <svg width={80} height={80} viewBox="0 0 80 80">
    {/* Gate symbols - simplified AND/OR gates */}
    <path d="M10,20 L30,20 L30,10 Q45,15 30,20 L30,30 L10,30 Z" fill="none" stroke={color} strokeWidth={1.5} opacity={opacity} />
    <path d="M50,20 L65,20 L65,10 Q78,15 65,20 L65,30 L50,30 Z" fill="none" stroke={color} strokeWidth={1.5} opacity={opacity} />
    <path d="M10,50 L30,50 L30,40 Q45,45 30,50 L30,60 L10,60 Z" fill="none" stroke={color} strokeWidth={1.5} opacity={opacity} />
    <path d="M50,50 L65,50 L65,40 Q78,45 65,50 L65,60 L50,60 Z" fill="none" stroke={color} strokeWidth={1.5} opacity={opacity} />
    {/* Connecting wires */}
    <line x1={30} y1={25} x2={50} y2={25} stroke={color} strokeWidth={1} opacity={opacity * 0.6} />
    <line x1={30} y1={55} x2={50} y2={55} stroke={color} strokeWidth={1} opacity={opacity * 0.6} />
    <line x1={65} y1={25} x2={75} y2={40} stroke={color} strokeWidth={1} opacity={opacity * 0.6} />
    <line x1={65} y1={55} x2={75} y2={40} stroke={color} strokeWidth={1} opacity={opacity * 0.6} />
    <circle cx={75} cy={40} r={3} fill={color} opacity={opacity * 0.5} />
  </svg>
);

const ShieldCheck: React.FC<{ color: string; opacity: number }> = ({ color, opacity }) => (
  <svg width={50} height={60} viewBox="0 0 50 60">
    <path
      d="M25,4 L46,16 L46,32 Q46,50 25,56 Q4,50 4,32 L4,16 Z"
      fill="none" stroke={color} strokeWidth={2} opacity={opacity}
    />
    {/* Checkmark */}
    <polyline
      points="15,30 22,38 35,22"
      fill="none" stroke={color} strokeWidth={2.5} strokeLinecap="round" strokeLinejoin="round"
      opacity={opacity}
    />
  </svg>
);

const NeuralNetwork: React.FC<{ color: string; opacity: number }> = ({ color, opacity }) => (
  <svg width={60} height={60} viewBox="0 0 60 60">
    {/* Layer 1 - input */}
    {[15, 30, 45].map((y) => (
      <circle key={`l1-${y}`} cx={10} cy={y} r={4} fill="none" stroke={color} strokeWidth={1.5} opacity={opacity} />
    ))}
    {/* Layer 2 - hidden */}
    {[12, 24, 36, 48].map((y) => (
      <circle key={`l2-${y}`} cx={30} cy={y} r={4} fill="none" stroke={color} strokeWidth={1.5} opacity={opacity} />
    ))}
    {/* Layer 3 - output */}
    {[20, 40].map((y) => (
      <circle key={`l3-${y}`} cx={50} cy={y} r={4} fill="none" stroke={color} strokeWidth={1.5} opacity={opacity} />
    ))}
    {/* Connections L1 -> L2 */}
    {[15, 30, 45].map((y1) =>
      [12, 24, 36, 48].map((y2) => (
        <line key={`c1-${y1}-${y2}`} x1={14} y1={y1} x2={26} y2={y2} stroke={color} strokeWidth={0.5} opacity={opacity * 0.3} />
      ))
    )}
    {/* Connections L2 -> L3 */}
    {[12, 24, 36, 48].map((y1) =>
      [20, 40].map((y2) => (
        <line key={`c2-${y1}-${y2}`} x1={34} y1={y1} x2={46} y2={y2} stroke={color} strokeWidth={0.5} opacity={opacity * 0.3} />
      ))
    )}
  </svg>
);

const CodeBrackets: React.FC<{ color: string; opacity: number }> = ({ color, opacity }) => (
  <svg width={80} height={80} viewBox="0 0 80 80">
    {/* Left curly brace */}
    <path
      d="M25,10 Q15,10 15,20 L15,32 Q15,40 8,40 Q15,40 15,48 L15,60 Q15,70 25,70"
      fill="none" stroke={color} strokeWidth={2.5} strokeLinecap="round" opacity={opacity}
    />
    {/* Right curly brace */}
    <path
      d="M55,10 Q65,10 65,20 L65,32 Q65,40 72,40 Q65,40 65,48 L65,60 Q65,70 55,70"
      fill="none" stroke={color} strokeWidth={2.5} strokeLinecap="round" opacity={opacity}
    />
    {/* Code lines inside */}
    <line x1={32} y1={28} x2={52} y2={28} stroke={color} strokeWidth={1.5} opacity={opacity * 0.5} />
    <line x1={32} y1={40} x2={48} y2={40} stroke={color} strokeWidth={1.5} opacity={opacity * 0.5} />
    <line x1={32} y1={52} x2={50} y2={52} stroke={color} strokeWidth={1.5} opacity={opacity * 0.5} />
  </svg>
);

const ICON_MAP: Record<IconType, React.FC<{ color: string; opacity: number }>> = {
  document_code: DocumentCode,
  document_text: DocumentText,
  gear: Gear,
  gate_cluster: GateCluster,
  shield_check: ShieldCheck,
  neural_network: NeuralNetwork,
  code_brackets: CodeBrackets,
};

// Icon dimensions for centering
const ICON_DIMENSIONS: Record<IconType, { width: number; height: number }> = {
  document_code: { width: 70, height: 90 },
  document_text: { width: 70, height: 90 },
  gear: { width: 60, height: 60 },
  gate_cluster: { width: 80, height: 80 },
  shield_check: { width: 50, height: 60 },
  neural_network: { width: 60, height: 60 },
  code_brackets: { width: 80, height: 80 },
};

export const StageIcon: React.FC<StageIconProps> = ({ icon, color, opacity }) => {
  const IconComponent = ICON_MAP[icon];
  const dims = ICON_DIMENSIONS[icon];
  return (
    <div style={{
      width: dims.width,
      height: dims.height,
      marginLeft: -dims.width / 2,
      marginTop: -dims.height / 2,
    }}>
      <IconComponent color={color} opacity={opacity} />
    </div>
  );
};

export { ICON_DIMENSIONS };
export default StageIcon;
