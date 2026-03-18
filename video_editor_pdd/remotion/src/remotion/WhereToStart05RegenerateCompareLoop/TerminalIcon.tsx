import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

export const TerminalIcon: React.FC<{
  startFrame: number;
}> = ({ startFrame }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  const scale = localFrame < 0
    ? 0
    : interpolate(localFrame, [0, 12], [0, 1], {
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      });

  const opacity = localFrame < 0
    ? 0
    : interpolate(localFrame, [0, 8], [0, 1], {
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      });

  // Particles burst
  const particles = [0, 1, 2, 3, 4].map((i) => {
    const particleDelay = 8 + i * 2;
    const pf = localFrame - particleDelay;
    const py = pf < 0
      ? 0
      : interpolate(pf, [0, 20], [0, 20 + i * 6], {
          extrapolateRight: "clamp",
        });
    const px = pf < 0
      ? 0
      : interpolate(pf, [0, 20], [0, (i - 2) * 8], {
          extrapolateRight: "clamp",
        });
    const pOpacity = pf < 0
      ? 0
      : interpolate(pf, [0, 5, 20], [0, 0.3, 0], {
          extrapolateRight: "clamp",
        });
    return { x: px, y: py, opacity: pOpacity };
  });

  return (
    <div
      style={{
        width: 55,
        height: 65,
        transform: `scale(${scale})`,
        opacity,
        position: "relative",
      }}
    >
      <svg width={55} height={65} viewBox="0 0 55 65">
        {/* Terminal window */}
        <rect
          x={0}
          y={0}
          width={55}
          height={45}
          rx={4}
          fill="#0F172A"
          stroke="#334155"
          strokeWidth={1.5}
        />
        {/* Title bar */}
        <rect x={0} y={0} width={55} height={10} rx={4} fill="#1E293B" />
        <rect x={0} y={6} width={55} height={4} fill="#1E293B" />
        {/* Title bar dots */}
        <circle cx={8} cy={5} r={1.5} fill="#EF4444" fillOpacity={0.5} />
        <circle cx={14} cy={5} r={1.5} fill="#EAB308" fillOpacity={0.5} />
        <circle cx={20} cy={5} r={1.5} fill="#22C55E" fillOpacity={0.5} />
        {/* Command text */}
        <text
          x={6}
          y={24}
          fontSize={6}
          fontFamily="monospace"
          fill="#5AAA6E"
          fillOpacity={0.6}
        >
          $ pdd generate
        </text>
        {/* Output lines */}
        <rect x={6} y={30} width={30} height={1.5} rx={0.75} fill="#4A90D9" fillOpacity={0.2} />
        <rect x={6} y={35} width={22} height={1.5} rx={0.75} fill="#4A90D9" fillOpacity={0.15} />

        {/* Particles */}
        {particles.map((p, i) => (
          <circle
            key={i}
            cx={27.5 + p.x}
            cy={48 + p.y}
            r={2}
            fill="#4A90D9"
            fillOpacity={p.opacity}
          />
        ))}
      </svg>
    </div>
  );
};
