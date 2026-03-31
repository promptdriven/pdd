import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

const DIVIDER_COLOR = "#3B82F6";
const DIVIDER_START = 0;
const DIVIDER_END = 18;
const FADE_OUT_START = 120;
const FADE_OUT_END = 150;
const COMP_WIDTH = 1920;
const CENTER_Y = 540;

export const AnimatedDivider: React.FC = () => {
	const frame = useCurrentFrame();

	const width = interpolate(frame, [DIVIDER_START, DIVIDER_END], [0, 420], {
		extrapolateLeft: "clamp",
		extrapolateRight: "clamp",
		easing: Easing.out(Easing.poly(3)),
	});

	const opacity = interpolate(frame, [DIVIDER_START, DIVIDER_START + 4, FADE_OUT_START, FADE_OUT_END], [0.7, 1, 1, 0], {
		extrapolateLeft: "clamp",
		extrapolateRight: "clamp",
	});

	const glowIntensity = interpolate(
		frame,
		[30, 60, 90, 120],
		[0, 12, 8, 12],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
		}
	);

	return (
		<div
			style={{
				position: "absolute",
				top: CENTER_Y - 20,
				left: COMP_WIDTH / 2 - width / 2,
				width,
				height: 3,
				backgroundColor: DIVIDER_COLOR,
				opacity,
				borderRadius: 2,
				boxShadow: `0 0 ${glowIntensity}px ${DIVIDER_COLOR}`,
			}}
		/>
	);
};
