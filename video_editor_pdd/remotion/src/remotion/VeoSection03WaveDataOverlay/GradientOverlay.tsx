import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { ANIMATION } from './constants';

export const GradientOverlay: React.FC = () => {
	const frame = useCurrentFrame();

	const overlayOpacity = interpolate(
		frame,
		[ANIMATION.overlayFadeStart, ANIMATION.overlayFadeEnd],
		[0.1, 0.6],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);

	return (
		<div
			style={{
				position: 'absolute',
				top: 0,
				left: 0,
				width: '100%',
				height: '100%',
				background: `linear-gradient(to bottom, transparent 0%, rgba(0, 0, 0, ${overlayOpacity}) 100%)`,
			}}
		/>
	);
};
