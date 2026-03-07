import React from "react";
import { AbsoluteFill } from "remotion";
import { BG_COLOR } from "./constants";
import { LeftPanel } from "./LeftPanel";
import { PanelLabels } from "./PanelLabels";
import { QuestionText } from "./QuestionText";
import { RightPanel } from "./RightPanel";
import { SplitLine } from "./SplitLine";

export const defaultColdOpen08ClosingQuestionCardProps = {};

/**
 * Closing Question Card — split-screen composition for the cold open's
 * thesis question: "Why are we still patching?"
 *
 * Left half: desaturated code-texture overlay (patching).
 * Right half: lighter panel with radial glow (building).
 * Center: bold question text spanning both halves.
 */
export const ColdOpen08ClosingQuestionCard: React.FC = () => {
	return (
		<AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
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
	);
};

export default ColdOpen08ClosingQuestionCard;
