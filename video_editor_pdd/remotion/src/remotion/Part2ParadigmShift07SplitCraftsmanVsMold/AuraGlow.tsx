import React from 'react';
import {useCurrentFrame, interpolate, Easing} from 'remotion';
import {
	AURA_APPEAR_START,
	AURA_APPEAR_END,
	AURA_INTENSIFY_START,
	AURA_INTENSIFY_END,
	AURA_MAX_OPACITY,
	AURA_INTENSE_OPACITY,
} from './constants';

interface AuraGlowProps {
	color: string;
	/**
	 * Vertical position of the aura center as percentage of panel height.
	 * 'lower' = 65% (chair/mold region), 'center' = 50%.
	 */
	position: 'lower' | 'center';
	/** Horizontal radius of the ellipse as % of panel width */
	radiusX?: number;
	/** Vertical radius of the ellipse as % of panel height */
	radiusY?: number;
}

const AuraGlow: React.FC<AuraGlowProps> = ({
	color,
	position,
	radiusX = 40,
	radiusY = 30,
}) => {
	const frame = useCurrentFrame();

	// Phase 1: appear (easeInOutCubic over 60 frames)
	const appearOpacity = interpolate(
		frame,
		[AURA_APPEAR_START, AURA_APPEAR_END],
		[0, AURA_MAX_OPACITY],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.bezier(0.65, 0, 0.35, 1), // cubic ease-in-out
		},
	);

	// Phase 2: intensify (easeInQuad over 60 frames)
	const intensifyOpacity = interpolate(
		frame,
		[AURA_INTENSIFY_START, AURA_INTENSIFY_END],
		[AURA_MAX_OPACITY, AURA_INTENSE_OPACITY],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.in(Easing.ease),
		},
	);

	// Use whichever phase we're in
	let opacity: number;
	if (frame < AURA_APPEAR_START) {
		opacity = 0;
	} else if (frame < AURA_INTENSIFY_START) {
		opacity = appearOpacity;
	} else {
		opacity = intensifyOpacity;
	}

	const cy = position === 'lower' ? '65%' : '50%';

	return (
		<div
			style={{
				position: 'absolute',
				top: 0,
				left: 0,
				width: '100%',
				height: '100%',
				pointerEvents: 'none',
			}}
		>
			<div
				style={{
					position: 'absolute',
					top: 0,
					left: 0,
					width: '100%',
					height: '100%',
					background: `radial-gradient(ellipse ${radiusX}% ${radiusY}% at 50% ${cy}, ${color} 0%, transparent 100%)`,
					opacity,
				}}
			/>
		</div>
	);
};

export default AuraGlow;
