import React from "react";
import {
  Easing,
  OffthreadVideo,
  interpolate,
  useCurrentFrame,
} from "remotion";
import {
  COST_LABEL_FADE_DURATION,
  COST_LABEL_START,
  FONT_INTER,
  HEADER_FADE_DURATION,
  HEADER_FADE_START,
  HEIGHT,
  SUBLABEL_COLOR,
  SUBLABEL_DELAY,
  SUBLABEL_FADE_DURATION,
} from "./constants";

type SplitPanelProps = {
  /** Pixel offset from left edge */
  x: number;
  /** Panel width in pixels */
  width: number;
  /** Header label, e.g. "DISCARD" */
  headerText: string;
  /** Accent color for header and cost label */
  accentColor: string;
  /** Color grade overlay color */
  colorGradeColor: string;
  /** Color grade opacity */
  colorGradeOpacity: number;
  /** Vignette edge color */
  vignetteEdge: string;
  /** Video source URL or null */
  videoSrc: string | null;
  /** Cost label text, e.g. "$2" */
  costLabel: string;
  /** Cost sub-label text, e.g. "new pair" */
  costSubLabel: string;
  /** Optional children rendered inside panel (e.g. terminal snippet) */
  children?: React.ReactNode;
};

const SplitPanel: React.FC<SplitPanelProps> = ({
  x,
  width,
  headerText,
  accentColor,
  colorGradeColor,
  colorGradeOpacity,
  vignetteEdge,
  videoSrc,
  costLabel,
  costSubLabel,
  children,
}) => {
  const frame = useCurrentFrame();

  // Header fade-in
  const headerOpacity = interpolate(
    frame,
    [HEADER_FADE_START, HEADER_FADE_START + HEADER_FADE_DURATION],
    [0, 0.3],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Cost label fade-in
  const costLabelOpacity = interpolate(
    frame,
    [COST_LABEL_START, COST_LABEL_START + COST_LABEL_FADE_DURATION],
    [0, 0.7],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Sub-label fade-in (delayed)
  const subLabelStart = COST_LABEL_START + SUBLABEL_DELAY;
  const subLabelOpacity = interpolate(
    frame,
    [subLabelStart, subLabelStart + SUBLABEL_FADE_DURATION],
    [0, 0.4],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: 0,
        width,
        height: HEIGHT,
        overflow: "hidden",
      }}
    >
      {/* Video background */}
      {videoSrc && (
        <OffthreadVideo
          src={videoSrc}
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: "100%",
            height: "100%",
            objectFit: "cover",
          }}
          muted
        />
      )}

      {/* Fallback gradient if no video */}
      {!videoSrc && (
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: "100%",
            height: "100%",
            background: `linear-gradient(135deg, ${colorGradeColor}22 0%, ${vignetteEdge} 100%)`,
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
          backgroundColor: colorGradeColor,
          opacity: colorGradeOpacity,
        }}
      />

      {/* Vignette overlay */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          background: `radial-gradient(ellipse at center, transparent 40%, ${vignetteEdge} 100%)`,
          opacity: 0.25,
        }}
      />

      {/* Panel header */}
      <div
        style={{
          position: "absolute",
          top: 36,
          left: 0,
          width: "100%",
          textAlign: "center",
          fontFamily: FONT_INTER,
          fontSize: 12,
          fontWeight: 600,
          color: accentColor,
          opacity: headerOpacity,
          letterSpacing: 3,
        }}
      >
        {headerText}
      </div>

      {/* Cost label */}
      <div
        style={{
          position: "absolute",
          top: 960,
          left: 0,
          width: "100%",
          textAlign: "center",
          fontFamily: FONT_INTER,
          fontSize: 28,
          fontWeight: 700,
          color: accentColor,
          opacity: costLabelOpacity,
        }}
      >
        {costLabel}
      </div>

      {/* Cost sub-label */}
      <div
        style={{
          position: "absolute",
          top: 990,
          left: 0,
          width: "100%",
          textAlign: "center",
          fontFamily: FONT_INTER,
          fontSize: 11,
          fontWeight: 400,
          color: SUBLABEL_COLOR,
          opacity: subLabelOpacity,
        }}
      >
        {costSubLabel}
      </div>

      {/* Additional children (terminal snippet, etc.) */}
      {children}
    </div>
  );
};

export default SplitPanel;
