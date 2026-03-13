import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS } from './constants';
import { MotionStreak } from './MotionStreak';
import { SlidingSquare } from './SlidingSquare';

export const AnimationSection04SquareSlideRight: React.FC = () => {
	return (
		<AbsoluteFill
			style={{
				background: `radial-gradient(circle at center, ${COLORS.backgroundCenter} 0%, ${COLORS.backgroundEdge} 100%)`,
			}}
		>
			<MotionStreak />
			<SlidingSquare />
		</AbsoluteFill>
	);
};

export const defaultAnimationSection04SquareSlideRightProps = {};

export default AnimationSection04SquareSlideRight;
