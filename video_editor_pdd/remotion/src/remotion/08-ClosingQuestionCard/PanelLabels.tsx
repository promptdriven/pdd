import React from "react";
import { interpolate, useCurrentFrame } from "remotion";
import {
	FADE_OUT_END,
	FADE_OUT_START,
	LABEL_FADE_END,
	LABEL_FADE_START,
	LABEL_FONT_SIZE,
	LABEL_FONT_WEIGHT,
	LEFT_LABEL_COLOR,
	LEFT_LABEL_MAX_OPACITY,
	LEFT_LABEL_TEXT,
	LEFT_LABEL_X,
	LEFT_LABEL_Y,
	RIGHT_LABEL_COLOR,
	RIGHT_LABEL_MAX_OPACITY,
	RIGHT_LABEL_TEXT,
	RIGHT_LABEL_X,
	RIGHT_LABEL_Y,
} from "./constants";

export const PanelLabels: React.FC = () => {
	const frame = useCurrentFrame();

	// Labels use linear easing per spec
	const labelFadeIn = interpolate(
		frame,
		[LABEL_FADE_START, LABEL_FADE_END],
		[0, 1],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
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

	const leftLabelOpacity = labelFadeIn * LEFT_LABEL_MAX_OPACITY * fadeOut;
	const rightLabelOpacity = labelFadeIn * RIGHT_LABEL_MAX_OPACITY * fadeOut;

	return (
		<>
			{/* Left label — "patching" */}
			<div
				style={{
					position: "absolute",
					left: LEFT_LABEL_X,
					top: LEFT_LABEL_Y,
					fontFamily: "Inter, sans-serif",
					fontSize: LABEL_FONT_SIZE,
					fontWeight: LABEL_FONT_WEIGHT,
					color: LEFT_LABEL_COLOR,
					opacity: leftLabelOpacity,
				}}
			>
				{LEFT_LABEL_TEXT}
			</div>

			{/* Right label — "building" */}
			<div
				style={{
					position: "absolute",
					left: RIGHT_LABEL_X,
					top: RIGHT_LABEL_Y,
					fontFamily: "Inter, sans-serif",
					fontSize: LABEL_FONT_SIZE,
					fontWeight: LABEL_FONT_WEIGHT,
					color: RIGHT_LABEL_COLOR,
					opacity: rightLabelOpacity,
					textAlign: "right",
					transform: "translateX(-100%)",
				}}
			>
				{RIGHT_LABEL_TEXT}
			</div>
		</>
	);
};
