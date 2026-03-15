import React from 'react';
import { useCurrentFrame, interpolate, interpolateColors, Easing } from 'remotion';
import { CANVAS, COLORS, SHAPE, TIMING, GHOST } from './constants';

/**
 * Computes the border radius for a given effective frame.
 */
function getBorderRadius(effectiveFrame: number): number {
	return interpolate(
		effectiveFrame,
		[TIMING.morphStart, TIMING.morphEnd],
		[SHAPE.borderRadiusStart, SHAPE.borderRadiusEnd],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.inOut(Easing.cubic),
		},
	);
}

/**
 * Computes the fill color for a given effective frame.
 */
function getFillColor(effectiveFrame: number): string {
	return interpolateColors(
		effectiveFrame,
		[TIMING.morphStart, TIMING.morphEnd],
		[COLORS.shapeStart, COLORS.shapeEnd],
	);
}

/**
 * Computes the size for a given effective frame.
 */
function getSize(effectiveFrame: number): number {
	return interpolate(
		effectiveFrame,
		[TIMING.morphStart, TIMING.morphEnd],
		[SHAPE.startSize, SHAPE.endSize],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);
}

/**
 * Renders 3 ghost copies of the morphing shape at decreasing opacity,
 * each lagging 3 frames behind the previous (3, 6, 9 frames behind).
 * Ghosts appear during the morph phase and fade out during settle with easeOutExpo.
 */
export const GhostTrail: React.FC = () => {
	const frame = useCurrentFrame();

	// Ghost trails fade in at morph start, fade out during settle (easeOutExpo)
	const ghostVisibility = interpolate(
		frame,
		[TIMING.morphStart, TIMING.morphStart + 3, TIMING.settleStart, TIMING.settleEnd],
		[0, 1, 1, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.exp),
		},
	);

	if (ghostVisibility <= 0) {
		return null;
	}

	return (
		<>
			{GHOST.opacities.map((baseOpacity, i) => {
				const lag = (i + 1) * GHOST.lagFrames;
				const ghostFrame = Math.max(0, frame - lag);
				const radius = getBorderRadius(ghostFrame);
				const color = getFillColor(ghostFrame);
				const size = getSize(ghostFrame);

				return (
					<div
						key={i}
						style={{
							position: 'absolute',
							width: size,
							height: size,
							borderRadius: radius,
							backgroundColor: color,
							opacity: baseOpacity * ghostVisibility,
							top: CANVAS.centerY - size / 2,
							left: CANVAS.centerX - size / 2,
						}}
					/>
				);
			})}
		</>
	);
};
