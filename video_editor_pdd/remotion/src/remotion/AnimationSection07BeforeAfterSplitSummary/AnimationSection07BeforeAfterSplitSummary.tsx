import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';

import {
	BACKGROUND_COLOR,
	TEXT_COLOR,
	DIVIDER_START_X,
	DIVIDER_END_X,
	DIVIDER_WIDTH,
	DIVIDER_ANIMATION_FRAMES,
	HEADING_FONT_SIZE,
	LABEL_FONT_SIZE,
	FONT_WEIGHT,
	HEADING_TOP,
	HEADING_LEFT,
	CANVAS_WIDTH,
} from './constants';

export const defaultAnimationSection07BeforeAfterSplitSummaryProps = {};

export const AnimationSection07BeforeAfterSplitSummary: React.FC = () => {
	const frame = useCurrentFrame();

	const dividerX = interpolate(
		frame,
		[0, DIVIDER_ANIMATION_FRAMES],
		[DIVIDER_START_X, DIVIDER_END_X],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
		},
	);

	const leftCenterX = dividerX / 2;
	const rightCenterX = dividerX + (CANVAS_WIDTH - dividerX) / 2;

	return (
		<AbsoluteFill
			style={{
				backgroundColor: BACKGROUND_COLOR,
				fontFamily: 'sans-serif',
				color: TEXT_COLOR,
			}}
		>
			{/* Left panel */}
			<div
				style={{
					position: 'absolute',
					top: 0,
					left: 0,
					width: dividerX,
					height: '100%',
					backgroundColor: BACKGROUND_COLOR,
					display: 'flex',
					justifyContent: 'center',
					alignItems: 'center',
				}}
			>
				<div
					style={{
						fontSize: LABEL_FONT_SIZE,
						fontWeight: FONT_WEIGHT,
						color: TEXT_COLOR,
						position: 'absolute',
						left: leftCenterX,
						top: '50%',
						transform: 'translate(-50%, -50%)',
					}}
				>
					Before
				</div>
			</div>

			{/* Right panel */}
			<div
				style={{
					position: 'absolute',
					top: 0,
					left: dividerX,
					width: CANVAS_WIDTH - dividerX,
					height: '100%',
					backgroundColor: BACKGROUND_COLOR,
					display: 'flex',
					justifyContent: 'center',
					alignItems: 'center',
				}}
			>
				<div
					style={{
						fontSize: LABEL_FONT_SIZE,
						fontWeight: FONT_WEIGHT,
						color: TEXT_COLOR,
						position: 'absolute',
						left: rightCenterX - dividerX,
						top: '50%',
						transform: 'translate(-50%, -50%)',
					}}
				>
					After
				</div>
			</div>

			{/* Animated vertical divider */}
			<div
				style={{
					position: 'absolute',
					top: 0,
					left: dividerX - DIVIDER_WIDTH / 2,
					width: DIVIDER_WIDTH,
					height: '100%',
					backgroundColor: BACKGROUND_COLOR,
				}}
			/>

			{/* Section heading */}
			<div
				style={{
					position: 'absolute',
					top: HEADING_TOP,
					left: HEADING_LEFT,
					fontSize: HEADING_FONT_SIZE,
					fontWeight: FONT_WEIGHT,
					color: TEXT_COLOR,
				}}
			>
				Split Summary
			</div>
		</AbsoluteFill>
	);
};

export default AnimationSection07BeforeAfterSplitSummary;
