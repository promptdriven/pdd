import React from 'react';
import {AbsoluteFill, useCurrentFrame, Easing, interpolate} from 'remotion';
import {
	BG_COLOR,
	TEXT_DEFAULT,
	ANNOTATION_UNDERLINE,
	SANS_FONT,
	FRAME_ANNOTATION,
} from './constants';
import {CodePanel} from './CodePanel';
import {TestPanel} from './TestPanel';
import {TerminalStrip} from './TerminalStrip';

export const defaultClosing03CodeRegenerateWorkflowProps = {};

export const Closing03CodeRegenerateWorkflow: React.FC = () => {
	const frame = useCurrentFrame();

	// Annotation fade-in
	const annotationOpacity = interpolate(
		frame,
		[FRAME_ANNOTATION, FRAME_ANNOTATION + 18],
		[0, 0.5],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);

	const annotationSlide = interpolate(
		frame,
		[FRAME_ANNOTATION, FRAME_ANNOTATION + 18],
		[6, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);

	return (
		<AbsoluteFill
			style={{
				backgroundColor: BG_COLOR,
				overflow: 'hidden',
			}}
		>
			{/* Code block — left zone */}
			<CodePanel />

			{/* Test panel — right zone */}
			<TestPanel />

			{/* Terminal strip — bottom zone */}
			<TerminalStrip />

			{/* Annotation: "Never opened the file." */}
			{frame >= FRAME_ANNOTATION && (
				<div
					style={{
						position: 'absolute',
						left: 60,
						top: 760,
						width: 860,
						display: 'flex',
						flexDirection: 'column',
						alignItems: 'center',
						opacity: annotationOpacity,
						transform: `translateY(${annotationSlide}px)`,
					}}
				>
					<span
						style={{
							fontFamily: SANS_FONT,
							fontSize: 16,
							fontStyle: 'italic',
							color: TEXT_DEFAULT,
							letterSpacing: '0.02em',
						}}
					>
						Never opened the file.
					</span>
					<div
						style={{
							width: 200,
							height: 1,
							backgroundColor: ANNOTATION_UNDERLINE,
							opacity: 0.15,
							marginTop: 4,
						}}
					/>
				</div>
			)}
		</AbsoluteFill>
	);
};

export default Closing03CodeRegenerateWorkflow;
