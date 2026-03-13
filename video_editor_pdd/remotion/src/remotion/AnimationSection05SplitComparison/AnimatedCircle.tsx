import React from 'react';
import { COLORS, SHAPES } from './constants';

export const AnimatedCircle: React.FC = () => {
	return (
		<div
			style={{
				position: 'absolute',
				left: SHAPES.circleCenterX - SHAPES.circleRadius,
				top: SHAPES.circleCenterY - SHAPES.circleRadius,
				width: SHAPES.circleRadius * 2,
				height: SHAPES.circleRadius * 2,
				borderRadius: '50%',
				backgroundColor: COLORS.circleFill,
			}}
		/>
	);
};
