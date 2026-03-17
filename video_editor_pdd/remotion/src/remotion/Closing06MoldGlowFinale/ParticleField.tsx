import React, {useMemo} from 'react';
import {useCurrentFrame, interpolate, Easing} from 'remotion';
import {
	PARTICLE_COUNT,
	PARTICLE_COLORS,
	PARTICLE_SPEED_MIN,
	PARTICLE_SPEED_MAX,
	PARTICLE_SIZE_MIN,
	PARTICLE_SIZE_MAX,
	PARTICLE_SPAWN_Y_MIN,
	PARTICLE_SPAWN_Y_MAX,
	PARTICLE_OPACITY_MIN,
	PARTICLE_OPACITY_MAX,
	WIDTH,
	DURATION_FRAMES,
} from './constants';

interface Particle {
	x: number;
	startY: number;
	speed: number;
	size: number;
	color: string;
	baseOpacity: number;
	spawnFrame: number;
}

function seededRandom(seed: number): number {
	const x = Math.sin(seed * 9301 + 49297) * 49297;
	return x - Math.floor(x);
}

export const ParticleField: React.FC = () => {
	const frame = useCurrentFrame();

	const particles = useMemo<Particle[]>(() => {
		return Array.from({length: PARTICLE_COUNT}, (_, i) => {
			const r1 = seededRandom(i * 7 + 1);
			const r2 = seededRandom(i * 13 + 2);
			const r3 = seededRandom(i * 19 + 3);
			const r4 = seededRandom(i * 23 + 4);
			const r5 = seededRandom(i * 31 + 5);
			const r6 = seededRandom(i * 37 + 6);
			const r7 = seededRandom(i * 41 + 7);

			return {
				x: r1 * WIDTH,
				startY:
					PARTICLE_SPAWN_Y_MIN +
					r2 * (PARTICLE_SPAWN_Y_MAX - PARTICLE_SPAWN_Y_MIN),
				speed:
					PARTICLE_SPEED_MIN +
					r3 * (PARTICLE_SPEED_MAX - PARTICLE_SPEED_MIN),
				size:
					PARTICLE_SIZE_MIN +
					r4 * (PARTICLE_SIZE_MAX - PARTICLE_SIZE_MIN),
				color: PARTICLE_COLORS[Math.floor(r5 * PARTICLE_COLORS.length)],
				baseOpacity:
					PARTICLE_OPACITY_MIN +
					r6 * (PARTICLE_OPACITY_MAX - PARTICLE_OPACITY_MIN),
				spawnFrame: Math.floor(r7 * 60), // stagger spawns over first 2s
			};
		});
	}, []);

	return (
		<>
			{particles.map((p, i) => {
				const activeFrame = frame - p.spawnFrame;
				if (activeFrame < 0) return null;

				const y = p.startY - activeFrame * p.speed;

				// Wrap particles that go off-screen
				const totalTravel = p.startY;
				const cycleLength = totalTravel / p.speed;
				const effectiveFrame = activeFrame % cycleLength;
				const effectiveY = p.startY - effectiveFrame * p.speed;

				if (effectiveY < -10) return null;

				// Fade out as particle approaches top
				const fadeZone = 200;
				const opacity =
					effectiveY < fadeZone
						? interpolate(effectiveY, [0, fadeZone], [0, p.baseOpacity], {
								extrapolateLeft: 'clamp',
								extrapolateRight: 'clamp',
								easing: Easing.out(Easing.quad),
							})
						: p.baseOpacity;

				// Fade in at spawn
				const spawnFade = interpolate(activeFrame, [0, 30], [0, 1], {
					extrapolateLeft: 'clamp',
					extrapolateRight: 'clamp',
				});

				return (
					<div
						key={i}
						style={{
							position: 'absolute',
							left: p.x - p.size / 2,
							top: effectiveY - p.size / 2,
							width: p.size,
							height: p.size,
							borderRadius: '50%',
							backgroundColor: p.color,
							opacity: opacity * spawnFade,
						}}
					/>
				);
			})}
		</>
	);
};
