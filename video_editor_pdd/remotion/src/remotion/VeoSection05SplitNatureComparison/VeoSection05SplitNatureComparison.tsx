import React from 'react';
import { AbsoluteFill, useVideoConfig } from 'remotion';
import { COLORS, resolveSplitNatureComparisonLayout } from './constants';
import { HeaderText } from './HeaderText';
import { SplitPanel } from './SplitPanel';
import { VerticalDivider } from './VerticalDivider';
import { PanelLabel } from './PanelLabel';
import { useVisualContractData, useVisualMediaSrc } from '../_shared/visual-runtime';

type SplitSideData = {
  label?: string;
};

type SplitVisualData = {
  background?: string;
  title?: string;
  heading?: string;
  left?: SplitSideData;
  right?: SplitSideData;
  leftPanel?: SplitSideData;
  rightPanel?: SplitSideData;
};

const asObject = (value: unknown): Record<string, unknown> | null => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    return null;
  }
  return value as Record<string, unknown>;
};

const asString = (value: unknown): string | null => {
  return typeof value === 'string' && value.trim().length > 0 ? value : null;
};

const resolvePanelData = (
  contract: SplitVisualData | null,
  side: 'left' | 'right',
): SplitSideData | null => {
  const primary = side === 'left' ? contract?.left : contract?.right;
  const fallback = side === 'left' ? contract?.leftPanel : contract?.rightPanel;
  return (asObject(primary) as SplitSideData | null) ?? (asObject(fallback) as SplitSideData | null);
};

export const VeoSection05SplitNatureComparison: React.FC = () => {
  const { width, height } = useVideoConfig();
  const layout = resolveSplitNatureComparisonLayout(width, height);
  const contract = useVisualContractData<SplitVisualData>();

  const defaultSrc = useVisualMediaSrc('defaultSrc');
  const leftSrc = useVisualMediaSrc('leftSrc', defaultSrc ?? undefined);
  const rightSrc = useVisualMediaSrc('rightSrc');
  const headingText = asString(contract?.heading) ?? asString(contract?.title);
  const backgroundColor = asString(contract?.background) ?? COLORS.background;
  const leftLabel =
    asString(resolvePanelData(contract, 'left')?.label) ?? 'Ocean · Sunset';
  const rightLabel =
    asString(resolvePanelData(contract, 'right')?.label) ?? 'Forest · Canopy';

  return (
    <AbsoluteFill style={{ backgroundColor }}>
      {headingText ? <HeaderText layout={layout} text={headingText} /> : null}

      {leftSrc ? (
        <SplitPanel side="left" videoSrc={leftSrc} layout={layout} />
      ) : null}

      {rightSrc ? (
        <SplitPanel side="right" videoSrc={rightSrc} layout={layout} />
      ) : null}

      <VerticalDivider layout={layout} />

      <PanelLabel text={leftLabel} side="left" layout={layout} />
      <PanelLabel text={rightLabel} side="right" layout={layout} />
    </AbsoluteFill>
  );
};

export const defaultVeoSection05SplitNatureComparisonProps = {};

export default VeoSection05SplitNatureComparison;
