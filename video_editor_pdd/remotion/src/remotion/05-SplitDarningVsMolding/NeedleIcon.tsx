import React from "react";

interface NeedleIconProps {
  color: string;
  size: number;
  opacity: number;
}

export const NeedleIcon: React.FC<NeedleIconProps> = ({
  color,
  size,
  opacity,
}) => {
  return (
    <svg
      width={size}
      height={size}
      viewBox="0 0 90 90"
      fill="none"
      style={{ opacity }}
    >
      {/* Needle */}
      <line
        x1={20}
        y1={70}
        x2={60}
        y2={15}
        stroke={color}
        strokeWidth={3}
        strokeLinecap="round"
      />
      {/* Needle eye */}
      <ellipse
        cx={60}
        cy={15}
        rx={4}
        ry={6}
        stroke={color}
        strokeWidth={2}
        fill="none"
      />
      {/* Thread trailing from needle */}
      <path
        d="M 56 18 Q 40 30 50 40 Q 60 50 45 55 Q 30 60 40 70"
        stroke={color}
        strokeWidth={2}
        fill="none"
        strokeLinecap="round"
        strokeDasharray="4 3"
      />
      {/* Cross stitches */}
      <line x1={30} y1={40} x2={42} y2={50} stroke={color} strokeWidth={2} strokeLinecap="round" />
      <line x1={42} y1={40} x2={30} y2={50} stroke={color} strokeWidth={2} strokeLinecap="round" />
      <line x1={38} y1={52} x2={50} y2={62} stroke={color} strokeWidth={2} strokeLinecap="round" />
      <line x1={50} y1={52} x2={38} y2={62} stroke={color} strokeWidth={2} strokeLinecap="round" />
    </svg>
  );
};

export default NeedleIcon;
