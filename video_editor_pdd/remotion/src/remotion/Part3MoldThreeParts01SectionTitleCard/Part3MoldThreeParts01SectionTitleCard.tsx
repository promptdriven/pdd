import React from "react";
import {
	AbsoluteFill,
	Sequence,
	useCurrentFrame,
	interpolate,
	Easing,
} from "remotion";
import {
	BG_COLOR,
	CANVAS_WIDTH,
	TITLE_COLOR,
	LABEL_COLOR,
	RULE_COLOR,
	FONT_FAMILY,
	TITLE_FONT_SIZE,
	LABEL_FONT_SIZE,
	LABEL_LETTER_SPACING,
	SECTION_LABEL,
	TITLE_LINE2,
	LABEL_Y,
	RULE_Y,
	TITLE_LINE2_Y,
	TITLE_LINE2_OFFSET_X,
	RULE_WIDTH,
	RULE_HEIGHT,
	BG_FADE_START,
	BG_FADE_END,
	LABEL_FADE_START,
	LABEL_FADE_END,
	RULE_DRAW_START,
	RULE_DRAW_END,
	LINE2_FADE_START,
	LINE2_FADE_END,
	LINE2_SLIDE_DISTANCE,
	TOTAL_FRAMES,
} from "./constants";
import { BlueprintGrid } from "./BlueprintGrid";
import { GhostShapes } from "./GhostShapes";
import { TypewriterText } from "./TypewriterText";

export const defaultPart3MoldThreeParts01SectionTitleCardProps = {};

export const Part3MoldThreeParts01SectionTitleCard: React.FC = () => {
	const frame = useCurrentFrame();

	// Background fade in
	const bgOpacity = interpolate(
		frame,
		[BG_FADE_START, BG_FADE_END],
		[0, 1],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.quad),
		},
	);

	// Section label fade in
	const labelOpacity = interpolate(
		frame,
		[LABEL_FADE_START, LABEL_FADE_END],
		[0, 0.5],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.quad),
		},
	);

	// Horizontal rule draw from center
	const ruleProgress = interpolate(
		frame,
		[RULE_DRAW_START, RULE_DRAW_END],
		[0, 1],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.inOut(Easing.quad),
		},
	);
	const ruleCurrentWidth = RULE_WIDTH * ruleProgress;

	// "THREE PARTS" fade + slide up
	const line2Opacity = interpolate(
		frame,
		[LINE2_FADE_START, LINE2_FADE_END],
		[0, 1],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.quad),
		},
	);
	const line2TranslateY = interpolate(
		frame,
		[LINE2_FADE_START, LINE2_FADE_END],
		[LINE2_SLIDE_DISTANCE, 0],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.cubic),
		},
	);

	return (
		<AbsoluteFill style={{ backgroundColor: "#000000" }}>
			<Sequence from={0} durationInFrames={TOTAL_FRAMES}>
				<AbsoluteFill
					style={{ backgroundColor: BG_COLOR, opacity: bgOpacity }}
				>
					{/* Blueprint grid */}
					<BlueprintGrid opacity={bgOpacity} />

					{/* Ghost shapes behind text */}
					<GhostShapes />

					{/* Section label: PART 3 */}
					<div
						style={{
							position: "absolute",
							top: LABEL_Y,
							left: 0,
							right: 0,
							width: CANVAS_WIDTH,
							display: "flex",
							justifyContent: "center",
							alignItems: "center",
							opacity: labelOpacity,
						}}
					>
						<span
							style={{
								fontFamily: FONT_FAMILY,
								fontSize: LABEL_FONT_SIZE,
								fontWeight: 600,
								color: LABEL_COLOR,
								letterSpacing: LABEL_LETTER_SPACING,
								transform: "translateY(-50%)",
							}}
						>
							{SECTION_LABEL}
						</span>
					</div>

					{/* Title line 1: THE MOLD HAS (typewriter) */}
					<TypewriterText />

					{/* Horizontal rule */}
					{frame >= RULE_DRAW_START && (
						<div
							style={{
								position: "absolute",
								top: RULE_Y,
								left: (CANVAS_WIDTH - ruleCurrentWidth) / 2,
								width: ruleCurrentWidth,
								height: RULE_HEIGHT,
								backgroundColor: RULE_COLOR,
								opacity: 0.5,
							}}
						/>
					)}

					{/* Title line 2: THREE PARTS */}
					<div
						style={{
							position: "absolute",
							top: TITLE_LINE2_Y,
							left: TITLE_LINE2_OFFSET_X,
							right: 0,
							width: CANVAS_WIDTH,
							display: "flex",
							justifyContent: "center",
							alignItems: "center",
							opacity: line2Opacity,
							transform: `translateY(${line2TranslateY}px)`,
						}}
					>
						<span
							style={{
								fontFamily: FONT_FAMILY,
								fontSize: TITLE_FONT_SIZE,
								fontWeight: 700,
								color: TITLE_COLOR,
								transform: "translateY(-50%)",
							}}
						>
							{TITLE_LINE2}
						</span>
					</div>
				</AbsoluteFill>
			</Sequence>
		</AbsoluteFill>
	);
};

export default Part3MoldThreeParts01SectionTitleCard;
