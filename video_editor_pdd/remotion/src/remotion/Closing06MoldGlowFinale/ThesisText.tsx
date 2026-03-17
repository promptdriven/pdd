import React from 'react';
import {useCurrentFrame, interpolate, Easing} from 'remotion';
import {
	THESIS_TEXT,
	THESIS_FONT_SIZE,
	THESIS_COLOR,
	THESIS_OPACITY,
	THESIS_Y,
	HR_WIDTH,
	HR_Y,
	HR_COLOR,
	HR_OPACITY,
	WIDTH,
} from './constants';

export const ThesisText: React.FC = () => {
	const frame = useCurrentFrame();

	// Horizontal rule draws from center outward over 12 frames
	const hrProgress = interpolate(frame, [0, 12], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.cubic),
	});

	const hrCurrentWidth = HR_WIDTH * hrProgress;

	// Text fades in after 8 frames (within this Sequence), over 20 frames
	const textOpacity = interpolate(frame, [8, 28], [0, THESIS_OPACITY], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	return (
		<div
			style={{
				position: 'absolute',
				top: 0,
				left: 0,
				width: 1920,
				height: 1080,
			}}
		>
			{/* Horizontal rule */}
			<div
				style={{
					position: 'absolute',
					left: WIDTH / 2 - hrCurrentWidth / 2,
					top: HR_Y,
					width: hrCurrentWidth,
					height: 1,
					backgroundColor: HR_COLOR,
					opacity: HR_OPACITY,
				}}
			/>

			{/* Thesis text */}
			<div
				style={{
					position: 'absolute',
					top: THESIS_Y,
					left: 0,
					width: WIDTH,
					textAlign: 'center',
					fontFamily: 'Inter, sans-serif',
					fontSize: THESIS_FONT_SIZE,
					fontWeight: 400,
					color: THESIS_COLOR,
					opacity: textOpacity,
				}}
			>
				{THESIS_TEXT}
			</div>
		</div>
	);
};
