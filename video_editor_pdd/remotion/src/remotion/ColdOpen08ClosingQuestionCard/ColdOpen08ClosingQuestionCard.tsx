import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile, Sequence } from "remotion";
import { LeftPanel } from "./LeftPanel";
import { PanelLabels } from "./PanelLabels";
import { QuestionText } from "./QuestionText";
import { RightPanel } from "./RightPanel";
import { SplitLine } from "./SplitLine";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";

export const defaultColdOpen08ClosingQuestionCardProps = {};

/**
 * Closing Question Card — split-screen composition for the cold open's
 * thesis question: "Why are we still patching?"
 *
 * Left half: desaturated code-texture overlay (patching).
 * Right half: lighter panel with radial glow (building).
 * Center: bold question text spanning both halves.
 * Background: Veo cold_open footage.
 */
export const ColdOpen08ClosingQuestionCard: React.FC = () => {
	return (
		<AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
			{/* Veo background video */}
			<AbsoluteFill>
				<OffthreadVideo
					src={staticFile("veo/cold_open.mp4")}
					style={{ width: "100%", height: "100%", objectFit: "cover" }}
				/>
			</AbsoluteFill>

			{/* Split-screen overlay — 90 frames (3s at 30fps) */}
			<Sequence from={0} durationInFrames={TOTAL_FRAMES}>
				<AbsoluteFill>
					{/* Left panel — patching (desaturated, code texture) */}
					<LeftPanel />

					{/* Right panel — building (lighter, radial glow) */}
					<RightPanel />

					{/* Vertical split line */}
					<SplitLine />

					{/* Center question text */}
					<QuestionText />

					{/* Bottom corner labels */}
					<PanelLabels />
				</AbsoluteFill>
			</Sequence>
		</AbsoluteFill>
	);
};

export default ColdOpen08ClosingQuestionCard;
