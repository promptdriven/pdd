import React from "react";
import { Easing, interpolate, useCurrentFrame } from "remotion";
import {
	CANVAS_HEIGHT,
	CANVAS_WIDTH,
	FADE_OUT_END,
	FADE_OUT_START,
	PANEL_FADE_END,
	PANEL_FADE_START,
	RADIAL_GLOW_COLOR,
	RADIAL_GLOW_OPACITY,
	RIGHT_PANEL_BG,
	SPLIT_X,
} from "./constants";

export const RightPanel: React.FC = () => {
	const frame = useCurrentFrame();

	const fadeIn = interpolate(
		frame,
		[PANEL_FADE_START, PANEL_FADE_END],
		[0, 1],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.cubic),
		},
	);

	const fadeOut = interpolate(
		frame,
		[FADE_OUT_START, FADE_OUT_END],
		[1, 0],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
		},
	);

	const opacity = fadeIn * fadeOut;
	const panelWidth = CANVAS_WIDTH - SPLIT_X;

	return (
		<div
			style={{
				position: "absolute",
				right: 0,
				top: 0,
				width: panelWidth,
				height: CANVAS_HEIGHT,
				backgroundColor: RIGHT_PANEL_BG,
				opacity,
				overflow: "hidden",
			}}
		>
			{/* Radial glow from center-right at 5% opacity */}
			<div
				style={{
					position: "absolute",
					top: "50%",
					left: "60%",
					width: 800,
					height: 800,
					transform: "translate(-50%, -50%)",
					borderRadius: "50%",
					background: `radial-gradient(circle, ${RADIAL_GLOW_COLOR} 0%, transparent 70%)`,
					opacity: RADIAL_GLOW_OPACITY,
				}}
			/>
		</div>
	);
};
