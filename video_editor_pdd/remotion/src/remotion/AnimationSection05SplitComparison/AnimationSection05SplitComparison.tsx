import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, LAYOUT, TIMING } from './constants';
import { VerticalDivider } from './VerticalDivider';
import { AnimatedCircle } from './AnimatedCircle';
import { AnimatedSquare } from './AnimatedSquare';
import { FadeInLabel } from './FadeInLabel';

export const AnimationSection05SplitComparison: React.FC = () => {
	const frame = useCurrentFrame();

	// Entire layout slides up from y=1080 to y=0 over frames 0-12
	const slideY = interpolate(
		frame,
		[TIMING.slideUpStart, TIMING.slideUpEnd],
		[CANVAS.height, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.cubic),
		},
	);

	return (
		<AbsoluteFill style={{ backgroundColor: COLORS.outerBackground }}>
			<div
				style={{
					position: 'absolute',
					left: 0,
					top: 0,
					width: CANVAS.width,
					height: CANVAS.height,
					transform: `translateY(${slideY}px)`,
				}}
			>
				{/* Left panel: dark blue with circle */}
				<div
					style={{
						position: 'absolute',
						left: 0,
						top: 0,
						width: LAYOUT.panelWidth,
						height: CANVAS.height,
						backgroundColor: COLORS.leftBackground,
					}}
				>
					<AnimatedCircle />
				</div>

				{/* Right panel: dark indigo with rounded square */}
				<div
					style={{
						position: 'absolute',
						left: LAYOUT.panelWidth,
						top: 0,
						width: LAYOUT.panelWidth,
						height: CANVAS.height,
						backgroundColor: COLORS.rightBackground,
					}}
				>
					<AnimatedSquare />
				</div>

				{/* Vertical divider */}
				<VerticalDivider />

				{/* Labels */}
				<FadeInLabel
					text="Before"
					panelLeft={0}
					panelWidth={LAYOUT.panelWidth}
					fadeStart={TIMING.beforeLabelStart}
					fadeEnd={TIMING.beforeLabelEnd}
				/>
				<FadeInLabel
					text="After"
					panelLeft={LAYOUT.panelWidth}
					panelWidth={LAYOUT.panelWidth}
					fadeStart={TIMING.afterLabelStart}
					fadeEnd={TIMING.afterLabelEnd}
				/>
			</div>
		</AbsoluteFill>
	);
};

export const defaultAnimationSection05SplitComparisonProps = {};

export default AnimationSection05SplitComparison;
