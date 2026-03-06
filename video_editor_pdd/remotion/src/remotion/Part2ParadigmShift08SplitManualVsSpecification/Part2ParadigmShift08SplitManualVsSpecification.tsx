import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { IndustryColumn } from "./IndustryColumn";
import { ShiftDivider } from "./ShiftDivider";
import { BannerText } from "./BannerText";
import {
  LAYOUT_X,
  LAYOUT_Y,
  LAYOUT_W,
  LAYOUT_H,
  PANEL_RADIUS,
  PANEL_BG,
  PANEL_FADE_START,
  PANEL_FADE_END,
  BEFORE_ROW_Y,
  BEFORE_ROW_H,
  AFTER_ROW_Y,
  AFTER_ROW_H,
  BEFORE_TINT,
  AFTER_TINT,
  BEFORE_COLOR,
  AFTER_COLOR,
  COL1_SLIDE_START,
  COL1_SLIDE_END,
  COL2_SLIDE_START,
  COL2_SLIDE_END,
  COL3_SLIDE_START,
  COL3_SLIDE_END,
  COLUMN_DATA,
  COLUMNS,
  COLUMN_WIDTH,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const defaultPart2ParadigmShift08SplitManualVsSpecificationProps = {};

export const Part2ParadigmShift08SplitManualVsSpecification: React.FC = () => {
  const frame = useCurrentFrame();

  const panelOpacity = interpolate(
    frame,
    [PANEL_FADE_START, PANEL_FADE_END, FADEOUT_START, FADEOUT_END],
    [0, 0.85, 0.85, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const globalOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const slideStarts = [COL1_SLIDE_START, COL2_SLIDE_START, COL3_SLIDE_START];
  const slideEnds = [COL1_SLIDE_END, COL2_SLIDE_END, COL3_SLIDE_END];

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part2_paradigm_shift.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Overlay content */}
      <AbsoluteFill>
        {/* Backing panel */}
        <div
          style={{
            position: "absolute",
            left: LAYOUT_X,
            top: LAYOUT_Y,
            width: LAYOUT_W,
            height: LAYOUT_H,
            borderRadius: PANEL_RADIUS,
            backgroundColor: PANEL_BG,
            backdropFilter: "blur(12px)",
            WebkitBackdropFilter: "blur(12px)",
            opacity: panelOpacity,
          }}
        />

        {/* BEFORE row tint */}
        <div
          style={{
            position: "absolute",
            left: LAYOUT_X,
            top: BEFORE_ROW_Y,
            width: LAYOUT_W,
            height: BEFORE_ROW_H,
            backgroundColor: BEFORE_TINT,
            borderRadius: `${PANEL_RADIUS}px ${PANEL_RADIUS}px 0 0`,
            opacity: globalOpacity,
            pointerEvents: "none",
          }}
        />

        {/* AFTER row tint */}
        <div
          style={{
            position: "absolute",
            left: LAYOUT_X,
            top: AFTER_ROW_Y,
            width: LAYOUT_W,
            height: AFTER_ROW_H,
            backgroundColor: AFTER_TINT,
            borderRadius: `0 0 ${PANEL_RADIUS}px ${PANEL_RADIUS}px`,
            opacity: globalOpacity,
            pointerEvents: "none",
          }}
        />

        {/* BEFORE vertical label */}
        <div
          style={{
            position: "absolute",
            left: LAYOUT_X + 12,
            top: BEFORE_ROW_Y + BEFORE_ROW_H / 2,
            transform: "rotate(-90deg) translateX(-50%)",
            transformOrigin: "left center",
            fontFamily: "Inter, sans-serif",
            fontWeight: 700,
            fontSize: 14,
            color: BEFORE_COLOR,
            opacity: globalOpacity * 0.5,
            letterSpacing: "0.1em",
            whiteSpace: "nowrap",
          }}
        >
          BEFORE
        </div>

        {/* AFTER vertical label */}
        <div
          style={{
            position: "absolute",
            left: LAYOUT_X + 12,
            top: AFTER_ROW_Y + AFTER_ROW_H / 2,
            transform: "rotate(-90deg) translateX(-50%)",
            transformOrigin: "left center",
            fontFamily: "Inter, sans-serif",
            fontWeight: 700,
            fontSize: 14,
            color: AFTER_COLOR,
            opacity: globalOpacity * 0.5,
            letterSpacing: "0.1em",
            whiteSpace: "nowrap",
          }}
        >
          AFTER
        </div>

        {/* Industry columns */}
        {COLUMN_DATA.map((col, i) => (
          <IndustryColumn
            key={col.industry}
            x={COLUMNS[i].x}
            industry={col.industry}
            beforeIcon={col.beforeIcon}
            beforeText={col.beforeText}
            afterIcon={col.afterIcon}
            afterText={col.afterText}
            slideStart={slideStarts[i]}
            slideEnd={slideEnds[i]}
          />
        ))}

        {/* Divider with THE SHIFT label */}
        <ShiftDivider />

        {/* Bottom banner */}
        <BannerText />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift08SplitManualVsSpecification;
