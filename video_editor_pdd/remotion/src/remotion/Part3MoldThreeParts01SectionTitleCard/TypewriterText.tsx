import React from "react";
import { useCurrentFrame } from "remotion";
import {
	TITLE_COLOR,
	FONT_FAMILY,
	TITLE_FONT_SIZE,
	TITLE_LINE1,
	TITLE_LINE1_Y,
	TYPEWRITER_START,
	TYPEWRITER_CHAR_DELAY,
	CANVAS_WIDTH,
} from "./constants";

export const TypewriterText: React.FC = () => {
	const frame = useCurrentFrame();
	const elapsed = Math.max(0, frame - TYPEWRITER_START);
	const charsVisible = Math.min(
		Math.floor(elapsed / TYPEWRITER_CHAR_DELAY),
		TITLE_LINE1.length,
	);

	const visibleText = TITLE_LINE1.slice(0, charsVisible);
	const showCursor =
		charsVisible < TITLE_LINE1.length &&
		frame >= TYPEWRITER_START &&
		frame % 6 < 4;

	if (frame < TYPEWRITER_START) return null;

	return (
		<div
			style={{
				position: "absolute",
				top: TITLE_LINE1_Y,
				left: 0,
				right: 0,
				width: CANVAS_WIDTH,
				display: "flex",
				justifyContent: "center",
				alignItems: "center",
			}}
		>
			<span
				style={{
					fontFamily: FONT_FAMILY,
					fontSize: TITLE_FONT_SIZE,
					fontWeight: 700,
					color: TITLE_COLOR,
					whiteSpace: "pre",
					transform: "translateY(-50%)",
				}}
			>
				{visibleText}
				{showCursor && (
					<span style={{ opacity: 0.7, fontWeight: 300 }}>|</span>
				)}
			</span>
		</div>
	);
};

export default TypewriterText;
