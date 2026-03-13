import React from 'react';
import { COLORS, SHAPES } from './constants';

export const AnimatedSquare: React.FC = () => {
	return (
		<div
			style={{
				position: 'absolute',
				left: SHAPES.squareCenterX - SHAPES.squareSize / 2,
				top: SHAPES.squareCenterY - SHAPES.squareSize / 2,
				width: SHAPES.squareSize,
				height: SHAPES.squareSize,
				borderRadius: SHAPES.squareBorderRadius,
				backgroundColor: COLORS.squareFill,
			}}
		/>
	);
};
