import React from 'react';
import { AbsoluteFill } from 'remotion';
import { CANVAS, COLORS } from './constants';
import { GhostTrail } from './GhostTrail';
import { MorphShape } from './MorphShape';

export const AnimationSection03CircleToSquareMorph: React.FC = () => {
	return (
		<AbsoluteFill
			style={{
				background: `radial-gradient(circle at 50% 50%, ${COLORS.backgroundCenter} 0%, ${COLORS.backgroundEdge} 100%)`,
			}}
		>
			<div
				style={{
					position: 'relative',
					width: CANVAS.width,
					height: CANVAS.height,
				}}
			>
				<GhostTrail />
				<MorphShape />
			</div>
		</AbsoluteFill>
	);
};

export const defaultAnimationSection03CircleToSquareMorphProps = {};

export default AnimationSection03CircleToSquareMorph;
