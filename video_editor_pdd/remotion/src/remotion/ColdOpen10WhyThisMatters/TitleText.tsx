import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

const TEXT_PRIMARY = "#FFFFFF";
const TITLE_FONT_SIZE = 72;
const TITLE_START = 6;
const TITLE_END = 24;
const FADE_OUT_START = 120;
const FADE_OUT_END = 150;
const COMP_WIDTH = 1920;
const CENTER_Y = 540;

export const TitleText: React.FC = () => {
	const frame = useCurrentFrame();

	const titleOpacity = interpolate(
		frame,
		[TITLE_START, TITLE_END, FADE_OUT_START, FADE_OUT_END],
		[0, 1, 1, 0],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
		}
	);

	const titleY = interpolate(
		frame,
		[TITLE_START, TITLE_END],
		[20, 0],
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
				top: CENTER_Y - 100 + titleY,
				left: 0,
				width: COMP_WIDTH,
				textAlign: "center",
				opacity: titleOpacity,
			}}
		>
			<span
				style={{
					fontFamily: "Inter, Helvetica, Arial, sans-serif",
					fontSize: TITLE_FONT_SIZE,
					fontWeight: 700,
					color: TEXT_PRIMARY,
					letterSpacing: "-0.02em",
					lineHeight: 1.1,
				}}
			>
				Why This Matters
			</span>
		</div>
	);
};
