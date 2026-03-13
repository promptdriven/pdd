import React from 'react';
import { COLORS } from './constants';

interface GradientOverlayProps {
	width: number;
	height: number;
}

export const GradientOverlay: React.FC<GradientOverlayProps> = ({ width, height }) => {
	return (
		<div
			style={{
				position: 'absolute',
				top: 0,
				left: 0,
				width,
				height,
				background: `linear-gradient(to top, rgba(11, 29, 58, ${COLORS.backgroundOpacity}) 0%, rgba(11, 29, 58, 0) 100%)`,
			}}
		/>
	);
};
