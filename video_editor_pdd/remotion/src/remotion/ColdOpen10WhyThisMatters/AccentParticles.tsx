import React from "react";
import { useCurrentFrame, interpolate } from "remotion";

const ACCENT_BLUE = "#3B82F6";
const ACCENT_GREEN = "#22C55E";
const ACCENT_AMBER = "#F59E0B";
const COMP_WIDTH = 1920;
const COMP_HEIGHT = 1080;
const FADE_OUT_START = 120;
const FADE_OUT_END = 150;

interface Particle {
	x: number;
	y: number;
	size: number;
	color: string;
	delay: number;
	speed: number;
}

const PARTICLES: Particle[] = [
	{ x: 0.15, y: 0.25, size: 4, color: ACCENT_BLUE, delay: 10, speed: 0.3 },
	{ x: 0.82, y: 0.3, size: 3, color: ACCENT_GREEN, delay: 14, speed: 0.25 },
	{ x: 0.25, y: 0.72, size: 5, color: ACCENT_AMBER, delay: 8, speed: 0.35 },
	{ x: 0.78, y: 0.68, size: 3, color: ACCENT_BLUE, delay: 18, speed: 0.2 },
	{ x: 0.5, y: 0.18, size: 4, color: ACCENT_GREEN, delay: 12, speed: 0.28 },
	{ x: 0.1, y: 0.5, size: 3, color: ACCENT_AMBER, delay: 20, speed: 0.22 },
	{ x: 0.9, y: 0.5, size: 4, color: ACCENT_BLUE, delay: 6, speed: 0.32 },
	{ x: 0.4, y: 0.82, size: 3, color: ACCENT_GREEN, delay: 16, speed: 0.26 },
];

export const AccentParticles: React.FC = () => {
	const frame = useCurrentFrame();

	return (
		<>
			{PARTICLES.map((p, i) => {
				const appearStart = p.delay;
				const appearEnd = p.delay + 12;

				const opacity = interpolate(
					frame,
					[appearStart, appearEnd, FADE_OUT_START, FADE_OUT_END],
					[0, 0.6, 0.6, 0],
					{
						extrapolateLeft: "clamp",
						extrapolateRight: "clamp",
					}
				);

				const drift = Math.sin(frame * p.speed * 0.05) * 8;
				const driftY = Math.cos(frame * p.speed * 0.04 + i) * 6;

				return (
					<div
						key={i}
						style={{
							position: "absolute",
							left: p.x * COMP_WIDTH + drift,
							top: p.y * COMP_HEIGHT + driftY,
							width: p.size,
							height: p.size,
							borderRadius: "50%",
							backgroundColor: p.color,
							opacity,
							boxShadow: `0 0 ${p.size * 3}px ${p.color}`,
						}}
					/>
				);
			})}
		</>
	);
};
