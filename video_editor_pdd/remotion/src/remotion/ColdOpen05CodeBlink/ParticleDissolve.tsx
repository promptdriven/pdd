import React, { useMemo } from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
	CodeLine,
	PARTICLE_COUNT,
	PARTICLE_MIN_SIZE,
	PARTICLE_MAX_SIZE,
	PARTICLE_GRAVITY,
	PARTICLE_DRIFT_X,
	PARTICLE_DURATION,
	DELETE_START,
	LINE_HEIGHT,
	CODE_FONT_SIZE,
} from "./constants";

interface Particle {
	x: number;
	y: number;
	size: number;
	color: string;
	driftX: number;
	delay: number;
}

function seededRandom(seed: number): () => number {
	let s = seed;
	return () => {
		s = (s * 16807 + 0) % 2147483647;
		return (s - 1) / 2147483646;
	};
}

interface ParticleDissolveProps {
	codeLines: CodeLine[];
}

export const ParticleDissolve: React.FC<ParticleDissolveProps> = ({
	codeLines,
}) => {
	const frame = useCurrentFrame();

	// Generate particles deterministically
	const particles = useMemo<Particle[]>(() => {
		const rand = seededRandom(42);
		const result: Particle[] = [];

		// Collect all color samples from the code
		const colorSamples: string[] = [];
		codeLines.forEach((line) => {
			line.forEach((token) => {
				if (token.text.trim()) {
					colorSamples.push(token.color);
				}
			});
		});

		for (let i = 0; i < PARTICLE_COUNT; i++) {
			const lineIdx = Math.floor(rand() * codeLines.length);
			const x = 64 + rand() * 800;
			const y = lineIdx * LINE_HEIGHT + rand() * CODE_FONT_SIZE;
			const size =
				PARTICLE_MIN_SIZE +
				rand() * (PARTICLE_MAX_SIZE - PARTICLE_MIN_SIZE);
			const color =
				colorSamples[Math.floor(rand() * colorSamples.length)] ||
				"#C9D1D9";
			const driftX = (rand() - 0.5) * 2 * PARTICLE_DRIFT_X;
			const delay = rand() * 5; // slight stagger

			result.push({ x, y, size, color, driftX, delay });
		}

		return result;
	}, [codeLines]);

	const dissolveFrame = frame - DELETE_START;
	if (dissolveFrame < 0) return null;

	return (
		<div
			style={{
				position: "absolute",
				left: 0,
				top: 0,
				width: "100%",
				height: "100%",
				pointerEvents: "none",
			}}
		>
			{particles.map((p, i) => {
				const pFrame = Math.max(0, dissolveFrame - p.delay);
				if (pFrame <= 0) return null;

				// Gravity: accelerating downward
				const gravityY =
					0.5 * PARTICLE_GRAVITY * pFrame * pFrame;

				// Linear horizontal drift
				const driftXOffset = p.driftX * pFrame;

				// Fade out
				const opacity = interpolate(
					pFrame,
					[0, PARTICLE_DURATION],
					[1, 0],
					{
						extrapolateLeft: "clamp",
						extrapolateRight: "clamp",
						easing: Easing.in(Easing.cubic),
					},
				);

				if (opacity <= 0) return null;

				return (
					<div
						key={i}
						style={{
							position: "absolute",
							left: p.x + driftXOffset,
							top: p.y + gravityY,
							width: p.size,
							height: p.size,
							borderRadius: p.size / 2,
							backgroundColor: p.color,
							opacity,
						}}
					/>
				);
			})}
		</div>
	);
};

export default ParticleDissolve;
