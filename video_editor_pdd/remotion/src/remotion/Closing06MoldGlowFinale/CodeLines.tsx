import React from 'react';
import {useCurrentFrame, interpolate, Easing} from 'remotion';
import {
	TRIANGLE_CENTER,
	CODE_OPACITY_START,
	CODE_OPACITY_END,
	CODE_COLOR,
	CODE_DIM_DURATION,
	CODE_LINE_WIDTHS,
} from './constants';

const MAX_LINE_WIDTH = 260;
const LINE_HEIGHT = 14;
const LINE_GAP = 6;

export const CodeLines: React.FC = () => {
	const frame = useCurrentFrame();

	// Dimming animation (frames 0-60 within this sequence, globally 30-90)
	const dimProgress = interpolate(frame, [0, CODE_DIM_DURATION], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.in(Easing.quad),
	});

	const opacity =
		CODE_OPACITY_START +
		(CODE_OPACITY_END - CODE_OPACITY_START) * dimProgress;

	const totalHeight =
		CODE_LINE_WIDTHS.length * LINE_HEIGHT +
		(CODE_LINE_WIDTHS.length - 1) * LINE_GAP;
	const startY = TRIANGLE_CENTER.y - totalHeight / 2;

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
			{CODE_LINE_WIDTHS.map((widthFraction, i) => {
				const lineWidth = widthFraction * MAX_LINE_WIDTH;
				const y = startY + i * (LINE_HEIGHT + LINE_GAP);
				const x = TRIANGLE_CENTER.x - lineWidth / 2;

				return (
					<div
						key={i}
						style={{
							position: 'absolute',
							left: x,
							top: y,
							width: lineWidth,
							height: 2,
							borderRadius: 1,
							backgroundColor: CODE_COLOR,
							opacity,
						}}
					/>
				);
			})}
		</div>
	);
};
