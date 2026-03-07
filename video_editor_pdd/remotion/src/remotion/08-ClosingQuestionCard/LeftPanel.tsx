import React from "react";
import { Easing, interpolate, useCurrentFrame } from "remotion";
import {
	CANVAS_HEIGHT,
	CODE_LINE_COLOR,
	CODE_LINE_COUNT,
	CODE_LINE_INTERVAL,
	FADE_OUT_END,
	FADE_OUT_START,
	LEFT_PANEL_BG,
	PANEL_FADE_END,
	PANEL_FADE_START,
	SPLIT_X,
} from "./constants";

export const LeftPanel: React.FC = () => {
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

	return (
		<div
			style={{
				position: "absolute",
				left: 0,
				top: 0,
				width: SPLIT_X,
				height: CANVAS_HEIGHT,
				backgroundColor: LEFT_PANEL_BG,
				filter: "saturate(0.4)",
				opacity,
				overflow: "hidden",
			}}
		>
			{/* Code-line texture pattern */}
			{Array.from({ length: CODE_LINE_COUNT }).map((_, i) => (
				<div
					key={i}
					style={{
						position: "absolute",
						left: 0,
						top: i * CODE_LINE_INTERVAL,
						width: "100%",
						height: 1,
						backgroundColor: CODE_LINE_COLOR,
					}}
				/>
			))}
		</div>
	);
};
