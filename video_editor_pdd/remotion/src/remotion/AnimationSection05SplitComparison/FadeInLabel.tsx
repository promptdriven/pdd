import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, TYPOGRAPHY } from './constants';

interface FadeInLabelProps {
	text: string;
	panelLeft: number;
	panelWidth: number;
	fadeStart: number;
	fadeEnd: number;
}

export const FadeInLabel: React.FC<FadeInLabelProps> = ({
	text,
	panelLeft,
	panelWidth,
	fadeStart,
	fadeEnd,
}) => {
	const frame = useCurrentFrame();

	const opacity = interpolate(frame, [fadeStart, fadeEnd], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
	});

	return (
		<div
			style={{
				position: 'absolute',
				left: panelLeft,
				top: TYPOGRAPHY.labelY,
				width: panelWidth,
				textAlign: 'center',
				fontFamily: TYPOGRAPHY.fontFamily,
				fontSize: TYPOGRAPHY.fontSize,
				fontWeight: TYPOGRAPHY.fontWeight,
				color: COLORS.label,
				opacity: opacity * TYPOGRAPHY.labelOpacity,
				whiteSpace: 'nowrap',
			}}
		>
			{text}
		</div>
	);
};
