import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile } from "remotion";
import {
	CANVAS_HEIGHT,
	LEFT_PANEL_WIDTH,
	RIGHT_PANEL_WIDTH,
	RIGHT_PANEL_X,
	LEFT_COLOR_GRADE,
	LEFT_COLOR_GRADE_OPACITY,
	LEFT_VIGNETTE_COLOR,
	LEFT_VIGNETTE_OPACITY,
	RIGHT_COLOR_GRADE,
	RIGHT_COLOR_GRADE_OPACITY,
	RIGHT_VIGNETTE_COLOR,
	RIGHT_VIGNETTE_OPACITY,
} from "./constants";

interface VideoPanelProps {
	side: "left" | "right";
	src: string | null;
}

export const VideoPanel: React.FC<VideoPanelProps> = ({ side, src }) => {
	const isLeft = side === "left";
	const width = isLeft ? LEFT_PANEL_WIDTH : RIGHT_PANEL_WIDTH;
	const left = isLeft ? 0 : RIGHT_PANEL_X;
	const colorGrade = isLeft ? LEFT_COLOR_GRADE : RIGHT_COLOR_GRADE;
	const colorGradeOpacity = isLeft
		? LEFT_COLOR_GRADE_OPACITY
		: RIGHT_COLOR_GRADE_OPACITY;
	const vignetteColor = isLeft ? LEFT_VIGNETTE_COLOR : RIGHT_VIGNETTE_COLOR;
	const vignetteOpacity = isLeft ? LEFT_VIGNETTE_OPACITY : RIGHT_VIGNETTE_OPACITY;

	return (
		<div
			style={{
				position: "absolute",
				left,
				top: 0,
				width,
				height: CANVAS_HEIGHT,
				overflow: "hidden",
			}}
		>
			{/* Veo clip */}
			{src && (
				<OffthreadVideo
					src={src.startsWith("veo/") ? staticFile(src) : src}
					style={{
						width: "100%",
						height: "100%",
						objectFit: "cover",
					}}
				/>
			)}

			{/* Color grade overlay */}
			<div
				style={{
					position: "absolute",
					top: 0,
					left: 0,
					width: "100%",
					height: "100%",
					backgroundColor: colorGrade,
					opacity: colorGradeOpacity,
					pointerEvents: "none",
				}}
			/>

			{/* Radial vignette — edges darkened */}
			<div
				style={{
					position: "absolute",
					top: 0,
					left: 0,
					width: "100%",
					height: "100%",
					background: `radial-gradient(ellipse at center, transparent 40%, ${vignetteColor} 100%)`,
					opacity: vignetteOpacity,
					pointerEvents: "none",
				}}
			/>
		</div>
	);
};
