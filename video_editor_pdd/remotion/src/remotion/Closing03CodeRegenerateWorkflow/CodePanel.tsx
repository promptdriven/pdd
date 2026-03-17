import React, {useMemo} from 'react';
import {useCurrentFrame, Easing, interpolate} from 'remotion';
import {
	PANEL_BG,
	TEXT_DEFAULT,
	HEADER_COLOR,
	KEYWORD_BLUE,
	STRING_GREEN,
	BUG_RED,
	PASS_GREEN,
	MONO_FONT,
	CODE_PANEL,
	ORIGINAL_CODE,
	REGENERATED_CODE,
	FRAME_CODE_DISSOLVE_START,
	FRAME_CODE_STREAM_START,
	FRAME_ANNOTATION,
} from './constants';

const LINE_HEIGHT = 28;
const CODE_OFFSET_Y = 50;
const CODE_OFFSET_X = 20;

const getColor = (type: string): string => {
	switch (type) {
		case 'keyword': return KEYWORD_BLUE;
		case 'string': return STRING_GREEN;
		case 'comment': return HEADER_COLOR;
		case 'bug': return BUG_RED;
		default: return TEXT_DEFAULT;
	}
};

/** Dissolving character with upward drift */
const DissolveChar: React.FC<{
	char: string;
	charIndex: number;
	lineIndex: number;
	color: string;
	dissolveFrame: number;
}> = ({char, charIndex, lineIndex, color, dissolveFrame}) => {
	const frame = useCurrentFrame();
	const staggerDelay = lineIndex * 2 + charIndex * 0.3;
	const localFrame = frame - dissolveFrame - staggerDelay;

	const opacity = interpolate(localFrame, [0, 20], [0.7, 0], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.in(Easing.quad),
	});

	const yOffset = interpolate(localFrame, [0, 20], [0, -30], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.in(Easing.quad),
	});

	const xJitter = interpolate(localFrame, [0, 20], [0, (charIndex % 3 - 1) * 8], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
	});

	return (
		<span
			style={{
				color,
				opacity,
				display: 'inline-block',
				transform: `translate(${xJitter}px, ${yOffset}px)`,
				whiteSpace: 'pre',
			}}
		>
			{char}
		</span>
	);
};

/** A single code line that can dissolve or stream in */
const CodeLine: React.FC<{
	text: string;
	type: string;
	lineIndex: number;
	phase: 'original' | 'dissolving' | 'empty' | 'streaming';
	streamDelay: number;
}> = ({text, type, lineIndex, phase, streamDelay}) => {
	const frame = useCurrentFrame();
	const isBugLine = type === 'bug';
	const color = getColor(type);

	if (phase === 'empty') {
		return <div style={{height: LINE_HEIGHT}} />;
	}

	if (phase === 'dissolving') {
		return (
			<div
				style={{
					height: LINE_HEIGHT,
					display: 'flex',
					alignItems: 'center',
					paddingLeft: CODE_OFFSET_X,
					position: 'relative',
					...(isBugLine ? {
						backgroundColor: `${BUG_RED}14`,
						borderLeft: `2px solid ${BUG_RED}`,
					} : {}),
				}}
			>
				{text.split('').map((char, ci) => (
					<DissolveChar
						key={ci}
						char={char}
						charIndex={ci}
						lineIndex={lineIndex}
						color={color}
						dissolveFrame={FRAME_CODE_DISSOLVE_START}
					/>
				))}
			</div>
		);
	}

	if (phase === 'streaming') {
		const lineFrame = frame - FRAME_CODE_STREAM_START - streamDelay;
		const lineOpacity = interpolate(lineFrame, [0, 8], [0, 0.7], {
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		});
		const lineSlide = interpolate(lineFrame, [0, 8], [10, 0], {
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		});

		return (
			<div
				style={{
					height: LINE_HEIGHT,
					display: 'flex',
					alignItems: 'center',
					paddingLeft: CODE_OFFSET_X,
					opacity: lineOpacity,
					transform: `translateY(${lineSlide}px)`,
				}}
			>
				<span style={{color, whiteSpace: 'pre', fontSize: 12, fontFamily: MONO_FONT}}>
					{text}
				</span>
			</div>
		);
	}

	// 'original' phase
	return (
		<div
			style={{
				height: LINE_HEIGHT,
				display: 'flex',
				alignItems: 'center',
				paddingLeft: CODE_OFFSET_X,
				position: 'relative',
				...(isBugLine ? {
					backgroundColor: `${BUG_RED}14`,
					borderLeft: `2px solid ${BUG_RED}`,
				} : {}),
			}}
		>
			<span style={{color, opacity: 0.7, whiteSpace: 'pre', fontSize: 12, fontFamily: MONO_FONT}}>
				{text}
			</span>
		</div>
	);
};

export const CodePanel: React.FC = () => {
	const frame = useCurrentFrame();

	// Determine phase
	const dissolveEnd = FRAME_CODE_DISSOLVE_START + 55; // ~all chars dissolved by frame 155
	const streamEnd = FRAME_CODE_STREAM_START + REGENERATED_CODE.length * 3 + 10;

	const phase: 'original' | 'dissolving' | 'empty' | 'streaming' = useMemo(() => {
		if (frame < FRAME_CODE_DISSOLVE_START) return 'original';
		if (frame < FRAME_CODE_STREAM_START) return 'dissolving';
		if (frame < FRAME_CODE_STREAM_START + 2) return 'empty';
		return 'streaming';
	}, [frame]);

	// Layout fade-in
	const layoutOpacity = interpolate(frame, [0, 20], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	// File tab dot color
	const dotColor = frame >= FRAME_ANNOTATION ? PASS_GREEN : BUG_RED;
	const dotTransition = frame >= FRAME_ANNOTATION
		? interpolate(frame, [FRAME_ANNOTATION, FRAME_ANNOTATION + 15], [0, 1], {
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
		})
		: 0;

	const codeLines = phase === 'streaming' ? REGENERATED_CODE : ORIGINAL_CODE;

	return (
		<div
			style={{
				position: 'absolute',
				left: CODE_PANEL.x,
				top: CODE_PANEL.y,
				width: CODE_PANEL.width,
				height: CODE_PANEL.height,
				backgroundColor: `${PANEL_BG}66`,
				borderRadius: 8,
				opacity: layoutOpacity,
				overflow: 'hidden',
			}}
		>
			{/* Header */}
			<div
				style={{
					display: 'flex',
					alignItems: 'center',
					gap: 8,
					padding: '10px 16px',
					borderBottom: '1px solid rgba(100, 116, 139, 0.15)',
				}}
			>
				<div
					style={{
						width: 8,
						height: 8,
						borderRadius: '50%',
						backgroundColor: dotColor,
						opacity: frame >= FRAME_ANNOTATION ? 1 : 0.8,
						transition: 'background-color 0.3s',
					}}
				/>
				<span
					style={{
						fontFamily: MONO_FONT,
						fontSize: 11,
						color: HEADER_COLOR,
						opacity: 0.5,
					}}
				>
					user_parser.py
				</span>
			</div>

			{/* Code content */}
			<div style={{padding: '8px 0'}}>
				{phase === 'empty' ? (
					<div style={{height: CODE_PANEL.height - 50}} />
				) : (
					codeLines.map((line, i) => (
						<CodeLine
							key={`${phase}-${i}`}
							text={line.text}
							type={line.type}
							lineIndex={i}
							phase={phase}
							streamDelay={i * 3}
						/>
					))
				)}
			</div>
		</div>
	);
};

export default CodePanel;
