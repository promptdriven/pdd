import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import {
	CAVITY_LEFT,
	CAVITY_RIGHT,
	CAVITY_TOP,
	CAVITY_BOTTOM,
	MOLD_CENTER_X,
	LIQUID_COLOR,
	WALL_SEGMENTS,
} from './constants';

// Simple seeded pseudo-random for deterministic particles
function seededRandom(seed: number): number {
	const x = Math.sin(seed * 12.9898 + seed * 78.233) * 43758.5453;
	return x - Math.floor(x);
}

// Simplified 2D Perlin-like noise using sine harmonics
function noise2D(x: number, y: number, seed: number): number {
	return (
		Math.sin(x * 1.7 + y * 2.3 + seed * 0.7) * 0.3 +
		Math.sin(x * 3.1 - y * 1.9 + seed * 1.3) * 0.2 +
		Math.sin(x * 0.8 + y * 4.1 + seed * 2.1) * 0.15 +
		Math.cos(x * 2.5 + y * 0.6 + seed * 0.4) * 0.2
	);
}

interface Particle {
	id: number;
	startFrame: number;
	startX: number;
	speed: number;
	lateralBias: number;
	size: number;
	noiseSeed: number;
}

const PARTICLE_COUNT = 220;
const NOZZLE_WIDTH = 50;

const LiquidFlow: React.FC = () => {
	const frame = useCurrentFrame();

	// Generate deterministic particles
	const particles = useMemo<Particle[]>(() => {
		const result: Particle[] = [];
		for (let i = 0; i < PARTICLE_COUNT; i++) {
			const r1 = seededRandom(i * 7 + 1);
			const r2 = seededRandom(i * 13 + 2);
			const r3 = seededRandom(i * 19 + 3);
			const r4 = seededRandom(i * 23 + 4);
			const r5 = seededRandom(i * 31 + 5);
			result.push({
				id: i,
				startFrame: Math.floor(r1 * 180), // staggered entry over first 6s
				startX: MOLD_CENTER_X + (r2 - 0.5) * NOZZLE_WIDTH,
				speed: 1.5 + r3 * 2.5, // pixels per frame downward
				lateralBias: (r4 - 0.5) * 1.2,
				size: 2 + r5 * 4,
				noiseSeed: r1 * 100,
			});
		}
		return result;
	}, []);

	// Calculate cavity bounds for collision
	const cavityWidth = CAVITY_RIGHT - CAVITY_LEFT;
	const cavityHeight = CAVITY_BOTTOM - CAVITY_TOP;

	return (
		<svg
			width={1920}
			height={1080}
			viewBox="0 0 1920 1080"
			style={{ position: 'absolute', top: 0, left: 0 }}
		>
			<defs>
				<filter id="liquidGlow" x="-100%" y="-100%" width="300%" height="300%">
					<feGaussianBlur stdDeviation="3" result="blur" />
					<feMerge>
						<feMergeNode in="blur" />
						<feMergeNode in="SourceGraphic" />
					</feMerge>
				</filter>
				<radialGradient id="particleGrad" cx="50%" cy="50%" r="50%">
					<stop offset="0%" stopColor={LIQUID_COLOR} stopOpacity={0.7} />
					<stop offset="70%" stopColor={LIQUID_COLOR} stopOpacity={0.3} />
					<stop offset="100%" stopColor={LIQUID_COLOR} stopOpacity={0} />
				</radialGradient>
			</defs>

			{particles.map((p) => {
				const age = frame - p.startFrame;
				if (age < 0) return null;

				// Fade in over first 5 frames
				const fadeIn = Math.min(1, age / 5);

				// Base position: flows downward from nozzle
				const noiseScale = 0.04;
				const noiseSpeed = 0.03;
				const t = age * noiseSpeed;

				// Vertical progress
				let baseY = CAVITY_TOP + age * p.speed;

				// Noise displacement for turbulence
				const nx = noise2D(p.startX * noiseScale, t, p.noiseSeed);
				const ny = noise2D(t, p.startX * noiseScale + 50, p.noiseSeed + 10);

				let x = p.startX + nx * 40 + p.lateralBias * age * 0.5;
				let y = baseY + ny * 15;

				// Clamp to cavity bounds (simulate wall collision)
				const marginLeft = CAVITY_LEFT + 6;
				const marginRight = CAVITY_RIGHT - 6;
				const marginTop = CAVITY_TOP + 4;
				const marginBottom = CAVITY_BOTTOM - 4;

				// Handle left wall contour (step at y ~350)
				let effectiveLeft = marginLeft;
				if (y > CAVITY_TOP + 200 && y < CAVITY_TOP + 350) {
					effectiveLeft = marginLeft + ((y - (CAVITY_TOP + 200)) / 150) * 60;
				} else if (y >= CAVITY_TOP + 350) {
					effectiveLeft = marginLeft + 60;
				}

				// Handle right wall contour
				let effectiveRight = marginRight;
				if (y > CAVITY_TOP + 180 && y < CAVITY_TOP + 380) {
					effectiveRight =
						marginRight - ((y - (CAVITY_TOP + 180)) / 200) * 50;
				} else if (y >= CAVITY_TOP + 380) {
					effectiveRight = marginRight - 50;
				}

				// Clamp
				x = Math.max(effectiveLeft, Math.min(effectiveRight, x));
				y = Math.max(marginTop, Math.min(marginBottom, y));

				// Once settled at bottom, pile up
				const fillProgress = interpolate(frame, [0, 300], [0, 1], {
					extrapolateLeft: 'clamp',
					extrapolateRight: 'clamp',
				});
				const fillLine = CAVITY_BOTTOM - fillProgress * cavityHeight * 0.85;
				if (y > fillLine && age > 60) {
					// Particle has "settled" - position it at the fill line with some lateral noise
					y = fillLine + seededRandom(p.id * 41) * 10;
					x =
						effectiveLeft +
						seededRandom(p.id * 53) * (effectiveRight - effectiveLeft);
				}

				// Opacity: liquid particles at 0.5 base
				const opacity = fadeIn * 0.5;

				return (
					<circle
						key={p.id}
						cx={x}
						cy={y}
						r={p.size}
						fill="url(#particleGrad)"
						opacity={opacity}
						filter="url(#liquidGlow)"
					/>
				);
			})}
		</svg>
	);
};

export default LiquidFlow;
