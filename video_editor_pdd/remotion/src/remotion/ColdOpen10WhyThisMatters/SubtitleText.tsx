import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

const TEXT_SECONDARY = "#94A3B8";
const SUBTITLE_FONT_SIZE = 28;
const SUBTITLE_START = 16;
const SUBTITLE_END = 34;
const FADE_OUT_START = 120;
const FADE_OUT_END = 150;
const COMP_WIDTH = 1920;
const CENTER_Y = 540;

export const SubtitleText: React.FC = () => {
	const frame = useCurrentFrame();

	const subtitleOpacity = interpolate(
		frame,
		[SUBTITLE_START, SUBTITLE_END, FADE_OUT_START, FADE_OUT_END],
		[0, 0.85, 0.85, 0],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
		}
	);

	const subtitleY = interpolate(
		frame,
		[SUBTITLE_START, SUBTITLE_END],
		[14, 0],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.poly(3)),
		}
	);

	return (
		<div
			style={{
				position: "absolute",
				top: CENTER_Y + 10 + subtitleY,
				left: 0,
				width: COMP_WIDTH,
				textAlign: "center",
				opacity: subtitleOpacity,
			}}
		>
			<span
				style={{
					fontFamily: "Inter, Helvetica, Arial, sans-serif",
					fontSize: SUBTITLE_FONT_SIZE,
					fontWeight: 400,
					color: TEXT_SECONDARY,
					letterSpacing: "0.04em",
					textTransform: "uppercase" as const,
				}}
			>
				The shift that changes everything
			</span>
		</div>
	);
};
