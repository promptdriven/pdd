import React from "react";
import { Easing, interpolate, useCurrentFrame } from "remotion";
import {
	LABEL_BASE_OPACITY,
	LABEL_FONT_SIZE,
	LABEL_FONT_WEIGHT,
	LABEL_LETTER_SPACING,
	LABEL_Y,
	LEFT_PANEL_WIDTH,
	RIGHT_PANEL_WIDTH,
	RIGHT_PANEL_X,
	PULSE_DURATION,
	PULSE_MAX_OPACITY,
	PULSE_MIN_OPACITY,
	PULSE_START,
} from "./constants";

interface PanelLabelProps {
	text: string;
	color: string;
	side: "left" | "right";
}

export const PanelLabel: React.FC<PanelLabelProps> = ({
	text,
	color,
	side,
}) => {
	const frame = useCurrentFrame();
	const isLeft = side === "left";
	const panelWidth = isLeft ? LEFT_PANEL_WIDTH : RIGHT_PANEL_WIDTH;
	const left = isLeft ? 0 : RIGHT_PANEL_X;

	// Gentle pulse at end of sequence (frames 210-240)
	const pulseProgress = interpolate(
		frame,
		[PULSE_START, PULSE_START + PULSE_DURATION],
		[0, Math.PI * 2],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
		},
	);

	const pulseAmount =
		frame >= PULSE_START
			? interpolate(
					Math.sin(pulseProgress),
					[-1, 1],
					[PULSE_MIN_OPACITY, PULSE_MAX_OPACITY],
				)
			: LABEL_BASE_OPACITY;

	return (
		<div
			style={{
				position: "absolute",
				left,
				top: LABEL_Y,
				width: panelWidth,
				display: "flex",
				justifyContent: "center",
				alignItems: "center",
				fontFamily: "'Inter', sans-serif",
				fontSize: LABEL_FONT_SIZE,
				fontWeight: LABEL_FONT_WEIGHT,
				letterSpacing: LABEL_LETTER_SPACING,
				color,
				opacity: pulseAmount,
				textTransform: "uppercase",
			}}
		>
			{text}
		</div>
	);
};
