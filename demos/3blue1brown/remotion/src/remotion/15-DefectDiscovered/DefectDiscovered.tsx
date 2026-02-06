import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing, OffthreadVideo, staticFile } from "remotion";
import { MoldScene } from "./MoldScene";
import { DefectHighlight } from "./DefectHighlight";
import { COLORS, BEATS, MOLD, DefectDiscoveredPropsType } from "./constants";

/**
 * 15-DefectDiscovered: Production runs, a defective part ejects,
 * production pauses, the defect is highlighted, and the camera zooms in.
 *
 * Animation sequence:
 *   Frame 0-60:    Production continues (mold cycling, parts ejecting)
 *   Frame 60-120:  Defective part ejects with visible crack/missing corner
 *   Frame 120-180: Production pauses, red pulsing highlight + "DEFECT" label
 *   Frame 180-300: Zoom in on defect, hold. Other parts blur/fade.
 */
export const DefectDiscovered: React.FC<DefectDiscoveredPropsType> = ({
  showNarration = true,
}) => {
  const frame = useCurrentFrame();

  // --- Zoom transform (frames 180-300) ---
  // Scale from 1 to ~2.5, centered on the defective part position
  const moldBottom = MOLD.centerY + MOLD.halfHeight;
  const defectCenterX = MOLD.centerX;
  const defectCenterY = moldBottom + 80;

  const zoomScale = interpolate(
    frame,
    [BEATS.ZOOM_START, BEATS.ZOOM_START + 60],
    [1, 2.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Translate so the defect stays centered on screen during zoom
  // At scale S, to keep point (cx, cy) at screen center (960, 540):
  //   translateX = 960 - cx * S
  //   translateY = 540 - cy * S
  const translateX = interpolate(
    frame,
    [BEATS.ZOOM_START, BEATS.ZOOM_START + 60],
    [0, 960 - defectCenterX * 2.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );
  const translateY = interpolate(
    frame,
    [BEATS.ZOOM_START, BEATS.ZOOM_START + 60],
    [0, 540 - defectCenterY * 2.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // --- Narration fade-in ---
  const narrationOpacity = showNarration
    ? interpolate(
        frame,
        [BEATS.NARRATION_START, BEATS.NARRATION_START + 25],
        [0, 1],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.cubic),
        }
      )
    : 0;

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {/* Zooming container wrapping the mold scene and highlight */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: 1920,
          height: 1080,
          transform: `translate(${translateX}px, ${translateY}px) scale(${zoomScale})`,
          transformOrigin: "0 0",
        }}
      >
        <OffthreadVideo
          src={staticFile("veo_defect_discovered.mp4")}
          style={{ width: 1920, height: 1080, objectFit: "cover" }}
        />
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: 1920,
            height: 1080,
            background: "rgba(10, 10, 26, 0.4)",
          }}
        />
        <MoldScene />
        <DefectHighlight />
      </div>

      {/* Narration overlay (outside zoom so text stays readable) */}
      {narrationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 100,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: narrationOpacity,
          }}
        >
          <div
            style={{
              fontSize: 36,
              fontFamily: "sans-serif",
              fontWeight: 400,
              color: "rgba(255, 255, 255, 0.95)",
              lineHeight: 1.6,
              maxWidth: 900,
              margin: "0 auto",
              letterSpacing: 0.5,
            }}
          >
            And when there&apos;s a defect?
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
