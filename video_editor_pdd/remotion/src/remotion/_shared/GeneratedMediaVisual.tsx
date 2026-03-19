import React from "react";
import { AbsoluteFill, OffthreadVideo, useVideoConfig } from "remotion";

import {
  useVisualContractData,
  useVisualMediaAssetSrc,
} from "./visual-runtime";

type GeneratedMediaVisualConfig = Record<string, string | boolean>;

type PanelMetadata = {
  label: string | null;
  caption: string | null;
  costLabel: string | null;
  costSubLabel: string | null;
  terminalSnippet: string | null;
  crossedOutIcon: string | null;
};

const lowerThirdLayout = (width: number, height: number) => {
  const scaleX = width / 1920;
  const scaleY = height / 1080;

  return {
    leftPadding: Math.max(32, 80 * scaleX),
    barHeight: Math.max(48, 80 * scaleY),
    bottomOffset: Math.max(32, 120 * scaleY),
    fontSize: Math.max(18, 22 * Math.min(scaleX, scaleY)),
  };
};

function asRecord(value: unknown): Record<string, unknown> | null {
  return value && typeof value === "object" && !Array.isArray(value)
    ? (value as Record<string, unknown>)
    : null;
}

function asString(value: unknown): string | null {
  return typeof value === "string" && value.trim() ? value : null;
}

function resolveCounterValue(contract: Record<string, unknown> | null): number | null {
  const overlay = asRecord(contract?.overlay);
  const counter = asRecord(overlay?.counter);
  const values = Array.isArray(counter?.values)
    ? counter.values.filter(
        (value): value is number => typeof value === "number" && Number.isFinite(value)
      )
    : [];

  return values.length > 0 ? values[values.length - 1] : null;
}

export const GeneratedMediaVisual: React.FC<{
  config?: GeneratedMediaVisualConfig | null;
}> = ({ config }) => {
  const src = useVisualMediaAssetSrc("defaultSrc");
  const leftSrc = useVisualMediaAssetSrc("leftSrc");
  const rightSrc = useVisualMediaAssetSrc("rightSrc");
  const contract = useVisualContractData<Record<string, unknown>>();
  const { width, height } = useVideoConfig();
  const layout = lowerThirdLayout(width, height);
  const gradientOverlay = config?.gradientOverlay;
  const lowerThirdText =
    typeof config?.lowerThirdText === "string" ? config.lowerThirdText : null;
  const lightBloom = config?.lightBloom === true;
  const counterOverlay = config?.counterOverlay === true;
  const counterPosition =
    typeof config?.counterPosition === "string" ? config.counterPosition : "lower_right";
  const splitDividerWidth = Math.max(2, Math.round(width * 0.0012));
  const splitLabelInset = Math.max(32, width * 0.025);
  const splitLabelBottom = Math.max(32, height * 0.06);
  const splitLabelFontSize = Math.max(18, 22 * Math.min(width / 1920, height / 1080));
  const splitMetaFontSize = Math.max(18, 20 * Math.min(width / 1920, height / 1080));
  const counterValue = resolveCounterValue(contract);

  const resolvePanelData = (side: "left" | "right"): Record<string, unknown> | null => {
    const directKey = side === "left" ? "left" : "right";
    const panelKey = side === "left" ? "leftPanel" : "rightPanel";
    return asRecord(contract?.[directKey]) ?? asRecord(contract?.[panelKey]);
  };

  const resolvePanelMetadata = (side: "left" | "right"): PanelMetadata => {
    const panel = resolvePanelData(side);
    return {
      label: asString(panel?.label),
      caption: asString(panel?.caption),
      costLabel: asString(panel?.costLabel),
      costSubLabel: asString(panel?.costSubLabel),
      terminalSnippet: asString(panel?.terminalSnippet),
      crossedOutIcon: asString(panel?.crossedOutIcon),
    };
  };

  const leftPanel = resolvePanelMetadata("left");
  const rightPanel = resolvePanelMetadata("right");
  const isSplitVisual = Boolean(leftSrc && rightSrc);

  const renderSplitMetadata = (
    side: "left" | "right",
    panel: PanelMetadata
  ) => {
    if (
      !panel.label &&
      !panel.caption &&
      !panel.costLabel &&
      !panel.costSubLabel &&
      !panel.terminalSnippet &&
      !panel.crossedOutIcon
    ) {
      return null;
    }

    const alignedLeft = side === "left";
    const xStyle = alignedLeft
      ? { left: splitLabelInset }
      : { right: splitLabelInset };

    return (
      <div
        style={{
          position: "absolute",
          bottom: splitLabelBottom,
          display: "flex",
          flexDirection: "column",
          gap: 10,
          alignItems: alignedLeft ? "flex-start" : "flex-end",
          textAlign: alignedLeft ? "left" : "right",
          ...xStyle,
        }}
      >
        {panel.label ? (
          <div
            style={{
              padding: "10px 16px",
              borderRadius: 999,
              backgroundColor: "rgba(11,17,32,0.82)",
              color: "#FFFFFF",
              fontFamily: "'Inter', sans-serif",
              fontSize: splitLabelFontSize,
              fontWeight: 700,
              opacity: 0.96,
            }}
          >
            {panel.label}
          </div>
        ) : null}
        {panel.caption ? (
          <div
            style={{
              maxWidth: width * 0.24,
              color: "#F8FAFC",
              fontFamily: "'Inter', sans-serif",
              fontSize: splitMetaFontSize,
              fontWeight: 600,
              lineHeight: 1.2,
              opacity: 0.86,
            }}
          >
            {panel.caption}
          </div>
        ) : null}
        {panel.costLabel ? (
          <div
            style={{
              color: "#F8FAFC",
              fontFamily: "'Inter', sans-serif",
              fontSize: splitMetaFontSize,
              fontWeight: 700,
              opacity: 0.84,
            }}
          >
            {panel.costLabel}
          </div>
        ) : null}
        {panel.costSubLabel ? (
          <div
            style={{
              color: "#E2E8F0",
              fontFamily: "'Inter', sans-serif",
              fontSize: Math.max(18, splitMetaFontSize - 1),
              fontWeight: 500,
              opacity: 0.72,
            }}
          >
            {panel.costSubLabel}
          </div>
        ) : null}
        {panel.terminalSnippet ? (
          <div
            style={{
              padding: "10px 12px",
              borderRadius: 12,
              backgroundColor: "rgba(2, 6, 23, 0.78)",
              color: "#E2E8F0",
              fontFamily: "'JetBrains Mono', monospace",
              fontSize: Math.max(18, splitMetaFontSize - 2),
              lineHeight: 1.25,
              opacity: 0.82,
            }}
          >
            {panel.terminalSnippet}
          </div>
        ) : null}
        {panel.crossedOutIcon ? (
          <div
            style={{
              position: "relative",
              padding: "8px 12px",
              borderRadius: 999,
              border: "2px solid rgba(248,250,252,0.72)",
              color: "#F8FAFC",
              fontFamily: "'Inter', sans-serif",
              fontSize: Math.max(18, splitMetaFontSize - 1),
              fontWeight: 600,
              opacity: 0.84,
            }}
          >
            {panel.crossedOutIcon.replace(/_/g, " ")}
            <div
              style={{
                position: "absolute",
                left: 6,
                right: 6,
                top: "50%",
                height: 2,
                backgroundColor: "#EF4444",
                transform: "rotate(-18deg)",
                transformOrigin: "center",
              }}
            />
          </div>
        ) : null}
      </div>
    );
  };

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
              src={leftSrc!}
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
              src={rightSrc!}
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
          {renderSplitMetadata("left", leftPanel)}
          {renderSplitMetadata("right", rightPanel)}
        </>
      ) : src ? (
        <OffthreadVideo
          src={src}
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

      {counterOverlay && counterValue !== null ? (
        <div
          style={{
            position: "absolute",
            right: counterPosition === "lower_right" ? Math.max(32, width * 0.04) : Math.max(32, width * 0.04),
            bottom: counterPosition === "lower_right" ? Math.max(40, height * 0.08) : Math.max(40, height * 0.08),
            padding: "10px 14px",
            borderRadius: 12,
            backgroundColor: "rgba(2, 6, 23, 0.72)",
            color: "#F8FAFC",
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: Math.max(20, 24 * Math.min(width / 1920, height / 1080)),
            fontWeight: 700,
            letterSpacing: 0.8,
            opacity: 0.9,
          }}
        >
          {counterValue.toLocaleString()}
        </div>
      ) : null}
    </AbsoluteFill>
  );
};

export default GeneratedMediaVisual;
