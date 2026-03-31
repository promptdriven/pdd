import React from "react";
import { useCurrentFrame, interpolate } from "remotion";

const COMP_WIDTH = 1920;
const COMP_HEIGHT = 1080;
const FADE_OUT_START = 120;
const FADE_OUT_END = 150;

export const VignetteOverlay: React.FC = () => {
	const frame = useCurrentFrame();

	const vignetteOpacity = interpolate(
		frame,
		[0, 10, FADE_OUT_START, FADE_OUT_END],
		[0.3, 0.5, 0.5, 0],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
		}
	);

	return (
		<div
			style={{
				position: "absolute",
				top: 0,
				left: 0,
				width: COMP_WIDTH,
				height: COMP_HEIGHT,
				background: `radial-gradient(ellipse at center, transparent 30%, rgba(0,0,0,${vignetteOpacity}) 100%)`,
				pointerEvents: "none",
			}}
		/>
	);
};
