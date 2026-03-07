import React from "react";
import { Easing, interpolate, useCurrentFrame } from "remotion";
import {
	CANVAS_WIDTH,
	FADE_OUT_END,
	FADE_OUT_START,
	QUESTION_CENTER_Y,
	QUESTION_COLOR,
	QUESTION_DRIFT_Y,
	QUESTION_FADE_END,
	QUESTION_FADE_START,
	QUESTION_FONT_SIZE,
	QUESTION_FONT_WEIGHT,
	QUESTION_LETTER_SPACING,
	QUESTION_TEXT,
	QUESTION_TEXT_SHADOW,
} from "./constants";

export const QuestionText: React.FC = () => {
	const frame = useCurrentFrame();

	const fadeIn = interpolate(
		frame,
		[QUESTION_FADE_START, QUESTION_FADE_END],
		[0, 1],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.quad),
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

	const yOffset = interpolate(
		frame,
		[QUESTION_FADE_START, QUESTION_FADE_END],
		[QUESTION_DRIFT_Y, 0],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.quad),
		},
	);

	return (
		<div
			style={{
				position: "absolute",
				top: QUESTION_CENTER_Y,
				left: 0,
				width: CANVAS_WIDTH,
				display: "flex",
				justifyContent: "center",
				alignItems: "center",
				fontFamily: "Inter, sans-serif",
				fontSize: QUESTION_FONT_SIZE,
				fontWeight: QUESTION_FONT_WEIGHT,
				letterSpacing: QUESTION_LETTER_SPACING,
				color: QUESTION_COLOR,
				textShadow: QUESTION_TEXT_SHADOW,
				opacity,
				transform: `translateY(${yOffset}px)`,
			}}
		>
			{QUESTION_TEXT}
		</div>
	);
};
