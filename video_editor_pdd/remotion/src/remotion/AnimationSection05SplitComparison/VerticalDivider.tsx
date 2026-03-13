import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, LAYOUT, TIMING } from './constants';

export const VerticalDivider: React.FC = () => {
	const frame = useCurrentFrame();

	const opacity = interpolate(
		frame,
		[TIMING.slideUpStart, TIMING.slideUpEnd],
		[0, LAYOUT.dividerMaxOpacity],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.inOut(Easing.quad),
		},
	);

	return (
		<div
			style={{
				position: 'absolute',
				left: LAYOUT.panelWidth - LAYOUT.dividerWidth / 2,
				top: 0,
				width: LAYOUT.dividerWidth,
				height: CANVAS.height,
				backgroundColor: COLORS.divider,
				opacity,
			}}
		/>
	);
};
