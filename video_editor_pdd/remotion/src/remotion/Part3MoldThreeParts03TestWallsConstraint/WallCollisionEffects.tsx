import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
	COLLISION_EVENTS,
	WALL_SEGMENTS,
	type CollisionEvent,
} from './constants';

const FLASH_DURATION = 6;
const RIPPLE_DURATION = 15;
const RIPPLE_MAX_RADIUS = 40;
const RIPPLE_COUNT = 3;

interface RippleProps {
	cx: number;
	cy: number;
	startFrame: number;
	intensity: number;
}

const Ripple: React.FC<RippleProps> = ({ cx, cy, startFrame, intensity }) => {
	const frame = useCurrentFrame();
	const age = frame - startFrame;

	if (age < 0 || age > RIPPLE_DURATION) return null;

	return (
		<>
			{Array.from({ length: RIPPLE_COUNT }).map((_, i) => {
				const delay = i * 3;
				const rippleAge = age - delay;
				if (rippleAge < 0) return null;

				const progress = interpolate(
					rippleAge,
					[0, RIPPLE_DURATION - delay],
					[0, 1],
					{ extrapolateRight: 'clamp' }
				);

				const radius = interpolate(
					progress,
					[0, 1],
					[4, RIPPLE_MAX_RADIUS * (0.7 + i * 0.15)],
					{ extrapolateRight: 'clamp' }
				);

				const opacity = interpolate(progress, [0, 0.3, 1], [0.3, 0.2, 0], {
					extrapolateRight: 'clamp',
				});

				return (
					<circle
						key={i}
						cx={cx}
						cy={cy}
						r={radius}
						fill="none"
						stroke="#D9944A"
						strokeWidth={1.5}
						opacity={opacity * intensity}
					/>
				);
			})}
		</>
	);
};

/**
 * Renders collision flash and ripple effects on walls.
 * Returns wallFlashStates for the MoldStructure to use.
 */
const WallCollisionEffects: React.FC<{
	onFlashStates?: (states: Record<string, number>) => void;
}> = () => {
	const frame = useCurrentFrame();

	// Compute flash states for each wall
	const flashStates: Record<string, number> = {};

	COLLISION_EVENTS.forEach((evt) => {
		const age = frame - evt.frame;
		if (age >= 0 && age <= FLASH_DURATION) {
			const flashProgress = interpolate(age, [0, FLASH_DURATION], [1, 0], {
				extrapolateRight: 'clamp',
			});
			// Exponential decay for flash
			const flashIntensity =
				flashProgress * flashProgress * flashProgress * evt.intensity;
			flashStates[evt.wallId] = Math.max(
				flashStates[evt.wallId] || 0,
				flashIntensity
			);
		}
	});

	return (
		<svg
			width={1920}
			height={1080}
			viewBox="0 0 1920 1080"
			style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
		>
			{COLLISION_EVENTS.map((evt, idx) => {
				const seg = WALL_SEGMENTS.find((w) => w.id === evt.wallId);
				if (!seg) return null;

				const midX = (seg.x1 + seg.x2) / 2;
				const midY = (seg.y1 + seg.y2) / 2;

				return (
					<Ripple
						key={`${evt.wallId}-${idx}`}
						cx={midX}
						cy={midY}
						startFrame={evt.frame}
						intensity={evt.intensity}
					/>
				);
			})}
		</svg>
	);
};

/** Computes flash intensities for each wall at the current frame */
export function useWallFlashStates(frame: number): Record<string, number> {
	const flashStates: Record<string, number> = {};

	COLLISION_EVENTS.forEach((evt) => {
		const age = frame - evt.frame;
		if (age >= 0 && age <= FLASH_DURATION) {
			const flashProgress = interpolate(age, [0, FLASH_DURATION], [1, 0], {
				extrapolateRight: 'clamp',
			});
			const flashIntensity =
				flashProgress * flashProgress * flashProgress * evt.intensity;
			flashStates[evt.wallId] = Math.max(
				flashStates[evt.wallId] || 0,
				flashIntensity
			);
		}
	});

	// Also add a sustained soft glow for walls at the end (frame 300+)
	if (frame >= 300) {
		const glowProgress = interpolate(frame, [300, 360], [0, 0.3], {
			extrapolateRight: 'clamp',
		});
		WALL_SEGMENTS.forEach((seg) => {
			flashStates[seg.id] = Math.max(
				flashStates[seg.id] || 0,
				glowProgress
			);
		});
	}

	return flashStates;
}

export default WallCollisionEffects;
