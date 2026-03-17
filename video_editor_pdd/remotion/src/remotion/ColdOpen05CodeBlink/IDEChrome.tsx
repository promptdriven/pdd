import React from "react";
import {
	TAB_BAR_HEIGHT,
	STATUS_BAR_HEIGHT,
	TAB_BG_COLOR,
	TAB_ACTIVE_BG,
	TAB_BORDER_COLOR,
	TAB_TEXT_COLOR,
	TAB_FONT_SIZE,
	STATUS_BAR_BG,
	STATUS_TEXT_COLOR,
	STATUS_FONT_SIZE,
	UI_FONT,
	CODE_FONT,
	CANVAS_WIDTH,
	CANVAS_HEIGHT,
} from "./constants";

interface IDEChromeProps {
	children: React.ReactNode;
}

export const IDEChrome: React.FC<IDEChromeProps> = ({ children }) => {
	return (
		<div
			style={{
				position: "absolute",
				width: CANVAS_WIDTH,
				height: CANVAS_HEIGHT,
				display: "flex",
				flexDirection: "column",
			}}
		>
			{/* Tab bar */}
			<div
				style={{
					height: TAB_BAR_HEIGHT,
					backgroundColor: TAB_BG_COLOR,
					borderBottom: `1px solid ${TAB_BORDER_COLOR}`,
					display: "flex",
					alignItems: "flex-end",
					paddingLeft: 12,
				}}
			>
				{/* Active tab */}
				<div
					style={{
						backgroundColor: TAB_ACTIVE_BG,
						borderTop: `2px solid ${TAB_BORDER_COLOR}`,
						borderLeft: `1px solid ${TAB_BORDER_COLOR}`,
						borderRight: `1px solid ${TAB_BORDER_COLOR}`,
						borderBottom: "none",
						borderTopLeftRadius: 4,
						borderTopRightRadius: 4,
						padding: "8px 16px",
						display: "flex",
						alignItems: "center",
						gap: 6,
						marginBottom: -1,
					}}
				>
					{/* Python file icon */}
					<svg width={14} height={14} viewBox="0 0 14 14">
						<rect
							x={2}
							y={1}
							width={10}
							height={12}
							rx={1}
							fill="none"
							stroke="#3572A5"
							strokeWidth={1.2}
						/>
						<text
							x={7}
							y={9.5}
							textAnchor="middle"
							fill="#3572A5"
							fontSize={6}
							fontFamily={CODE_FONT}
							fontWeight={700}
						>
							py
						</text>
					</svg>
					<span
						style={{
							fontFamily: UI_FONT,
							fontSize: TAB_FONT_SIZE,
							color: TAB_TEXT_COLOR,
							opacity: 0.7,
						}}
					>
						user_parser.py
					</span>
				</div>
			</div>

			{/* Editor area */}
			<div
				style={{
					flex: 1,
					position: "relative",
					overflow: "hidden",
				}}
			>
				{children}
			</div>

			{/* Status bar */}
			<div
				style={{
					height: STATUS_BAR_HEIGHT,
					backgroundColor: STATUS_BAR_BG,
					borderTop: `1px solid ${TAB_BORDER_COLOR}`,
					display: "flex",
					alignItems: "center",
					paddingLeft: 16,
					paddingRight: 16,
				}}
			>
				<span
					style={{
						fontFamily: CODE_FONT,
						fontSize: STATUS_FONT_SIZE,
						color: STATUS_TEXT_COLOR,
						opacity: 0.3,
					}}
				>
					Ln 1, Col 1
				</span>
				<span
					style={{
						fontFamily: CODE_FONT,
						fontSize: STATUS_FONT_SIZE,
						color: STATUS_TEXT_COLOR,
						opacity: 0.3,
						marginLeft: "auto",
					}}
				>
					Python
				</span>
			</div>
		</div>
	);
};

export default IDEChrome;
