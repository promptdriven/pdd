import React from "react";
import {
	CANVAS_HEIGHT,
	SPLIT_LINE_COLOR,
	SPLIT_LINE_OPACITY,
	SPLIT_LINE_WIDTH,
	SPLIT_X,
} from "./constants";

export const SplitLine: React.FC = () => {
	return (
		<div
			style={{
				position: "absolute",
				left: SPLIT_X - SPLIT_LINE_WIDTH / 2,
				top: 0,
				width: SPLIT_LINE_WIDTH,
				height: CANVAS_HEIGHT,
				backgroundColor: SPLIT_LINE_COLOR,
				opacity: SPLIT_LINE_OPACITY,
			}}
		/>
	);
};
