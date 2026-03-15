import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile, useVideoConfig } from "remotion";

import { useVisualContractData, useVisualMediaSrc } from "./visual-runtime";

type GeneratedMediaVisualConfig = Record<string, string | boolean>;

const lowerThirdLayout = (width: number, height: number) => {
  const scaleX = width / 1920;
  const scaleY = height / 1080;

  return {
    leftPadding: Math.max(32, 80 * scaleX),
    barHeight: Math.max(48, 80 * scaleY),
    bottomOffset: Math.max(32, 120 * scaleY),
    fontSize: Math.max(16, 20 * Math.min(scaleX, scaleY)),
  };
};

export const GeneratedMediaVisual: React.FC<{
  config?: GeneratedMediaVisualConfig | null;
}> = ({ config }) => {
  const src = useVisualMediaSrc("defaultSrc");
  const leftSrc = useVisualMediaSrc("leftSrc");
  const rightSrc = useVisualMediaSrc("rightSrc");
  const contract = useVisualContractData<Record<string, unknown>>();
  const { width, height } = useVideoConfig();
  const layout = lowerThirdLayout(width, height);
  const gradientOverlay = config?.gradientOverlay;
  const lowerThirdText =
    typeof config?.lowerThirdText === "string" ? config.lowerThirdText : null;
  const lightBloom = config?.lightBloom === true;
  const splitDividerWidth = Math.max(2, Math.round(width * 0.0012));
  const splitLabelInset = Math.max(32, width * 0.025);
  const splitLabelBottom = Math.max(32, height * 0.06);
  const splitLabelFontSize = Math.max(16, 20 * Math.min(width / 1920, height / 1080));

  const resolvePanelLabel = (side: "left" | "right"): string | null => {
    const primaryKey = side === "left" ? "left" : "right";
    const panelKey = side === "left" ? "leftPanel" : "rightPanel";
    const primary = contract?.[primaryKey];
    const fallback = contract?.[panelKey];
    const source = (primary && typeof primary === "object" ? primary : fallback) as
      | Record<string, unknown>
      | undefined;
    const label = source?.label;
    return typeof label === "string" && label.trim() ? label : null;
  };

  const leftLabel = resolvePanelLabel("left");
  const rightLabel = resolvePanelLabel("right");
  const isSplitVisual = Boolean(leftSrc && rightSrc);

  return (
    <AbsoluteFill style={{ backgroundColor: "#000000" }}>
      {isSplitVisual ? (
        <>
          <div
            style={{
              position: "absolute",
              left: 0,
              top: 0,
              width: width / 2 - splitDividerWidth,
              height,
              overflow: "hidden",
            }}
          >
            <OffthreadVideo
              src={staticFile(leftSrc!)}
              style={{ width: "100%", height: "100%", objectFit: "cover" }}
            />
          </div>
          <div
            style={{
              position: "absolute",
              right: 0,
              top: 0,
              width: width / 2 - splitDividerWidth,
              height,
              overflow: "hidden",
            }}
          >
            <OffthreadVideo
              src={staticFile(rightSrc!)}
              style={{ width: "100%", height: "100%", objectFit: "cover" }}
            />
          </div>
          <div
            style={{
              position: "absolute",
              left: width / 2 - splitDividerWidth / 2,
              top: 0,
              width: splitDividerWidth,
              height,
              backgroundColor: "#C9A84C",
              opacity: 0.95,
              boxShadow: "0 0 24px rgba(201,168,76,0.35)",
            }}
          />
          {leftLabel ? (
            <div
              style={{
                position: "absolute",
                left: splitLabelInset,
                bottom: splitLabelBottom,
                padding: "10px 16px",
                borderRadius: 999,
                backgroundColor: "rgba(11,17,32,0.72)",
                color: "#FFFFFF",
                fontFamily: "'Inter', sans-serif",
                fontSize: splitLabelFontSize,
                fontWeight: 600,
              }}
            >
              {leftLabel}
            </div>
          ) : null}
          {rightLabel ? (
            <div
              style={{
                position: "absolute",
                right: splitLabelInset,
                bottom: splitLabelBottom,
                padding: "10px 16px",
                borderRadius: 999,
                backgroundColor: "rgba(11,17,32,0.72)",
                color: "#FFFFFF",
                fontFamily: "'Inter', sans-serif",
                fontSize: splitLabelFontSize,
                fontWeight: 600,
              }}
            >
              {rightLabel}
            </div>
          ) : null}
        </>
      ) : src ? (
        <OffthreadVideo
          src={staticFile(src)}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
        />
      ) : null}

      {gradientOverlay === "bottom" ? (
        <AbsoluteFill
          style={{
            background:
              "linear-gradient(180deg, rgba(10,22,40,0) 0%, rgba(10,22,40,0) 60%, rgba(10,22,40,0.6) 100%)",
            pointerEvents: "none",
          }}
        />
      ) : null}

      {lightBloom ? (
        <AbsoluteFill
          style={{
            background:
              "radial-gradient(circle at 82% 12%, rgba(255,220,150,0.18) 0%, rgba(255,220,150,0.08) 18%, rgba(255,220,150,0) 38%)",
            pointerEvents: "none",
          }}
        />
      ) : null}

      {lowerThirdText ? (
        <div
          style={{
            position: "absolute",
            left: 0,
            right: 0,
            bottom: layout.bottomOffset,
            height: layout.barHeight,
            backgroundColor: "rgba(0,0,0,0.5)",
            display: "flex",
            alignItems: "center",
            paddingLeft: layout.leftPadding,
            paddingRight: layout.leftPadding,
            color: "#FFFFFF",
            fontFamily: "'Inter', sans-serif",
            fontSize: layout.fontSize,
            fontWeight: 500,
            opacity: 0.9,
          }}
        >
          {lowerThirdText}
        </div>
      ) : null}
    </AbsoluteFill>
  );
};

export default GeneratedMediaVisual;
