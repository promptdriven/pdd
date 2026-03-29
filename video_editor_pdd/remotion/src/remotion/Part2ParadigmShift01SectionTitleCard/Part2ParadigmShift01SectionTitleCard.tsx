import React from 'react';
import {
	AbsoluteFill,
	useCurrentFrame,
	interpolate,
	Easing,
} from 'remotion';
import {BlueprintGrid} from './BlueprintGrid';
import {MoldSilhouette} from './MoldSilhouette';
import {
	BG_COLOR,
	CANVAS_WIDTH,
	TITLE_COLOR,
	LABEL_COLOR,
	LABEL_OPACITY,
	RULE_COLOR,
	RULE_OPACITY,
	TITLE_FONT_SIZE,
	LABEL_FONT_SIZE,
	LABEL_LETTER_SPACING,
	RULE_WIDTH,
	RULE_THICKNESS,
	LABEL_Y,
	TITLE_LINE1_Y,
	RULE_Y,
	TITLE_LINE2_Y,
	TITLE_LINE2_OFFSET_X,
	BG_FADE_START,
	BG_FADE_END,
	LABEL_FADE_START,
	LABEL_FADE_DURATION,
	MOLD_DRAW_START,
	TYPEWRITER_START,
	TYPEWRITER_CHAR_DELAY,
	RULE_DRAW_START,
	RULE_DRAW_DURATION,
	SHIFT_FADE_START,
	SHIFT_FADE_DURATION,
	FADEOUT_START,
	FADEOUT_DURATION,
	SECTION_LABEL,
	TITLE_LINE1,
	TITLE_LINE2,
} from './constants';

export const defaultPart2ParadigmShift01SectionTitleCardProps = {};

export const Part2ParadigmShift01SectionTitleCard: React.FC = () => {
	const frame = useCurrentFrame();

	// ── Background fade-in from black ───────────────────────
	const bgOpacity = interpolate(frame, [BG_FADE_START, BG_FADE_END], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
	});

	// ── Global fade-out at end ──────────────────────────────
	const fadeOutOpacity = interpolate(
		frame,
		[FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
		[1, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.in(Easing.quad),
		},
	);

	// ── "PART 2" label fade-in ──────────────────────────────
	const labelOpacity = interpolate(
		frame,
		[LABEL_FADE_START, LABEL_FADE_START + LABEL_FADE_DURATION],
		[0, LABEL_OPACITY],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);

	// ── "THE PARADIGM" typewriter ───────────────────────────
	const totalChars = TITLE_LINE1.length;
	const typewriterEnd =
		TYPEWRITER_START + totalChars * TYPEWRITER_CHAR_DELAY;
	const charsVisible =
		frame < TYPEWRITER_START
			? 0
			: Math.min(
					totalChars,
					Math.floor(
						(frame - TYPEWRITER_START) / TYPEWRITER_CHAR_DELAY,
					) + 1,
				);
	const paradigmText = TITLE_LINE1.slice(0, charsVisible);

	// ── Horizontal rule drawing from center ─────────────────
	const ruleProgress = interpolate(
		frame,
		[RULE_DRAW_START, RULE_DRAW_START + RULE_DRAW_DURATION],
		[0, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.inOut(Easing.quad),
		},
	);
	const ruleCurrentWidth = RULE_WIDTH * ruleProgress;

	// ── "SHIFT" fade-in + slide-up ──────────────────────────
	const shiftOpacity = interpolate(
		frame,
		[SHIFT_FADE_START, SHIFT_FADE_START + SHIFT_FADE_DURATION],
		[0, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);
	const shiftSlideY = interpolate(
		frame,
		[SHIFT_FADE_START, SHIFT_FADE_START + SHIFT_FADE_DURATION],
		[10, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.cubic),
		},
	);

	// Local frame for mold (starts at MOLD_DRAW_START)
	const moldLocalFrame = Math.max(0, frame - MOLD_DRAW_START);

	return (
		<AbsoluteFill
			style={{
				backgroundColor: '#000000',
			}}
		>
			<AbsoluteFill
				style={{
					opacity: bgOpacity * fadeOutOpacity,
					backgroundColor: BG_COLOR,
				}}
			>
				{/* Blueprint grid */}
				<BlueprintGrid />

				{/* Ghost mold silhouette */}
				{frame >= MOLD_DRAW_START && (
					<MoldSilhouette localFrame={moldLocalFrame} />
				)}

				{/* "PART 2" section label */}
				<div
					style={{
						position: 'absolute',
						top: LABEL_Y,
						left: 0,
						width: CANVAS_WIDTH,
						textAlign: 'center',
						fontFamily: 'Inter, sans-serif',
						fontSize: LABEL_FONT_SIZE,
						fontWeight: 600,
						color: LABEL_COLOR,
						opacity: labelOpacity,
						letterSpacing: LABEL_LETTER_SPACING,
						lineHeight: 1,
					}}
				>
					{SECTION_LABEL}
				</div>

				{/* "THE PARADIGM" typewriter text */}
				<div
					style={{
						position: 'absolute',
						top: TITLE_LINE1_Y,
						left: 0,
						width: CANVAS_WIDTH,
						textAlign: 'center',
						fontFamily: 'Inter, sans-serif',
						fontSize: TITLE_FONT_SIZE,
						fontWeight: 700,
						color: TITLE_COLOR,
						lineHeight: 1,
						whiteSpace: 'pre',
					}}
				>
					{paradigmText}
					{/* Typing cursor blink while typing */}
					{frame >= TYPEWRITER_START && frame < typewriterEnd + 10 && (
						<span
							style={{
								opacity: Math.sin(frame * 0.3) > 0 ? 0.8 : 0,
								color: TITLE_COLOR,
							}}
						>
							|
						</span>
					)}
				</div>

				{/* Horizontal rule — drawn from center outward */}
				{frame >= RULE_DRAW_START && (
					<div
						style={{
							position: 'absolute',
							top: RULE_Y,
							left: (CANVAS_WIDTH - ruleCurrentWidth) / 2,
							width: ruleCurrentWidth,
							height: RULE_THICKNESS,
							backgroundColor: RULE_COLOR,
							opacity: RULE_OPACITY,
						}}
					/>
				)}

				{/* "SHIFT" — fade-in with slide-up */}
				<div
					style={{
						position: 'absolute',
						top: TITLE_LINE2_Y + shiftSlideY,
						left: TITLE_LINE2_OFFSET_X,
						width: CANVAS_WIDTH,
						textAlign: 'center',
						fontFamily: 'Inter, sans-serif',
						fontSize: TITLE_FONT_SIZE,
						fontWeight: 700,
						color: TITLE_COLOR,
						opacity: shiftOpacity,
						lineHeight: 1,
					}}
				>
					{TITLE_LINE2}
				</div>
			</AbsoluteFill>
		</AbsoluteFill>
	);
};

export default Part2ParadigmShift01SectionTitleCard;
