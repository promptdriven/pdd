import React from 'react';
import {
	AbsoluteFill,
	Easing,
	Sequence,
	interpolate,
	useCurrentFrame,
} from 'remotion';
import { BlueprintGrid } from './BlueprintGrid';
import { GhostShapes } from './GhostShapes';
import {
	BG_COLOR,
	WIDTH,
	HEIGHT,
	TITLE_COLOR,
	TITLE_FONT,
	TITLE_SIZE,
	TITLE_WEIGHT,
	SECTION_LABEL_COLOR,
	LABEL_SIZE,
	LABEL_WEIGHT,
	LABEL_LETTER_SPACING,
	LABEL_Y,
	TITLE_LINE1_Y,
	RULE_Y,
	TITLE_LINE2_Y,
	TITLE_LINE2_OFFSET_X,
	RULE_WIDTH,
	RULE_HEIGHT,
	RULE_COLOR,
	BG_FADE_END,
	LABEL_FADE_START,
	LABEL_FADE_DURATION,
	GHOST_DRAW_START,
	TITLE1_TYPE_START,
	TITLE1_CHAR_DELAY,
	RULE_DRAW_START,
	RULE_DRAW_DURATION,
	TITLE2_FADE_START,
	TITLE2_FADE_DURATION,
	TITLE2_SLIDE_DISTANCE,
} from './constants';

// ─── Section Label ("PART 2") ────────────────────────────────────────

const SectionLabel: React.FC = () => {
	const frame = useCurrentFrame();

	const opacity = interpolate(frame, [0, LABEL_FADE_DURATION], [0, 0.5], {
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	return (
		<div
			style={{
				position: 'absolute',
				top: LABEL_Y,
				left: 0,
				width: WIDTH,
				textAlign: 'center',
				fontFamily: TITLE_FONT,
				fontSize: LABEL_SIZE,
				fontWeight: LABEL_WEIGHT,
				color: SECTION_LABEL_COLOR,
				letterSpacing: LABEL_LETTER_SPACING,
				opacity,
			}}
		>
			PART 2
		</div>
	);
};

// ─── Typewriter Title ("THE PARADIGM") ───────────────────────────────

const TITLE1_TEXT = 'THE PARADIGM';

const TypewriterTitle: React.FC = () => {
	const frame = useCurrentFrame();

	const charsVisible = Math.min(
		TITLE1_TEXT.length,
		Math.floor(frame / TITLE1_CHAR_DELAY) + 1,
	);

	const displayText = TITLE1_TEXT.slice(0, charsVisible);

	return (
		<div
			style={{
				position: 'absolute',
				top: TITLE_LINE1_Y,
				left: 0,
				width: WIDTH,
				textAlign: 'center',
				fontFamily: TITLE_FONT,
				fontSize: TITLE_SIZE,
				fontWeight: TITLE_WEIGHT,
				color: TITLE_COLOR,
			}}
		>
			{displayText}
		</div>
	);
};

// ─── Horizontal Rule ─────────────────────────────────────────────────

const HorizontalRule: React.FC = () => {
	const frame = useCurrentFrame();

	const progress = interpolate(frame, [0, RULE_DRAW_DURATION], [0, 1], {
		extrapolateRight: 'clamp',
		easing: Easing.inOut(Easing.quad),
	});

	const currentWidth = RULE_WIDTH * progress;

	return (
		<div
			style={{
				position: 'absolute',
				top: RULE_Y,
				left: (WIDTH - currentWidth) / 2,
				width: currentWidth,
				height: RULE_HEIGHT,
				backgroundColor: RULE_COLOR,
				opacity: 0.8,
				zIndex: 5,
			}}
		/>
	);
};

// ─── Slide-up + Fade-in Title ("SHIFT") ──────────────────────────────

const ShiftTitle: React.FC = () => {
	const frame = useCurrentFrame();

	const opacity = interpolate(frame, [0, TITLE2_FADE_DURATION], [0, 1], {
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	const translateY = interpolate(
		frame,
		[0, TITLE2_FADE_DURATION],
		[TITLE2_SLIDE_DISTANCE, 0],
		{
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.cubic),
		},
	);

	return (
		<div
			style={{
				position: 'absolute',
				top: TITLE_LINE2_Y,
				left: TITLE_LINE2_OFFSET_X,
				width: WIDTH,
				textAlign: 'center',
				fontFamily: TITLE_FONT,
				fontSize: TITLE_SIZE,
				fontWeight: TITLE_WEIGHT,
				color: TITLE_COLOR,
				opacity,
				transform: `translateY(${translateY}px)`,
			}}
		>
			SHIFT
		</div>
	);
};

// ─── Background Fade ─────────────────────────────────────────────────

const BackgroundFade: React.FC = () => {
	const frame = useCurrentFrame();

	// Black overlay that fades out to reveal the background
	const blackOpacity = interpolate(frame, [0, BG_FADE_END], [1, 0], {
		extrapolateRight: 'clamp',
	});

	return (
		<AbsoluteFill
			style={{
				backgroundColor: '#000000',
				opacity: blackOpacity,
				zIndex: 10,
			}}
		/>
	);
};

// ─── Main Component ──────────────────────────────────────────────────

export const defaultPart2ParadigmShift01SectionTitleCardProps = {};

export const Part2ParadigmShift01SectionTitleCard: React.FC = () => {
	return (
		<AbsoluteFill
			style={{
				backgroundColor: BG_COLOR,
				width: WIDTH,
				height: HEIGHT,
			}}
		>
			{/* Blueprint grid — visible from frame 0, fades in */}
			<BlueprintGrid />

			{/* Black overlay that fades out during frames 0-15 */}
			<BackgroundFade />

			{/* Ghost shapes — mold cavity + circuit schematic */}
			<Sequence from={GHOST_DRAW_START} durationInFrames={105}>
				<GhostShapes />
			</Sequence>

			{/* Section label "PART 2" */}
			<Sequence from={LABEL_FADE_START} durationInFrames={105}>
				<SectionLabel />
			</Sequence>

			{/* Title line 1: "THE PARADIGM" — typewriter */}
			<Sequence from={TITLE1_TYPE_START} durationInFrames={80}>
				<TypewriterTitle />
			</Sequence>

			{/* Horizontal rule — draws from center */}
			<Sequence from={RULE_DRAW_START} durationInFrames={60}>
				<HorizontalRule />
			</Sequence>

			{/* Title line 2: "SHIFT" — fade + slide up */}
			<Sequence from={TITLE2_FADE_START} durationInFrames={50}>
				<ShiftTitle />
			</Sequence>
		</AbsoluteFill>
	);
};

export default Part2ParadigmShift01SectionTitleCard;
