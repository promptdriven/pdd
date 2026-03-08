import React from 'react';
import { interpolate, useCurrentFrame } from 'remotion';

const AnimatedDivider: React.FC<{
	startX: number;
	endX: number;
	width: number;
	color: string;
	durationFrames: number;
}> = ({ startX, endX, width, color, durationFrames }) => {
	const frame = useCurrentFrame();

	const x = interpolate(frame, [0, durationFrames], [startX, endX], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
	});

	return (
		<div
			style={{
				position: 'absolute',
				top: 0,
				left: x - width / 2,
				width: width,
				height: '100%',
				backgroundColor: color,
			}}
		/>
	);
};

export default AnimatedDivider;
