import React from 'react';
import { Sequence } from 'remotion';
import { PlatformLabel } from './PlatformLabel';
import { MetricBar } from './MetricBar';
import { ANIMATION_TIMING } from './constants';

interface PlatformMetricsProps {
  platformName: string;
  yPosition: number;
  metrics: {
    Quality: number;
    Speed: number;
    Cost: number;
    Control: number;
  };
  startFrame: number;
}

export const PlatformMetrics: React.FC<PlatformMetricsProps> = ({
  platformName,
  yPosition,
  metrics,
  startFrame,
}) => {
  const metricOrder: Array<'Quality' | 'Speed' | 'Cost' | 'Control'> = [
    'Quality',
    'Speed',
    'Cost',
    'Control',
  ];

  return (
    <Sequence from={startFrame}>
      <PlatformLabel y={yPosition} text={platformName} />
      {metricOrder.map((metricName, index) => (
        <MetricBar
          key={`${platformName}-${metricName}`}
          metric={metricName}
          value={metrics[metricName]}
          yBase={yPosition + 40}
          metricIndex={index}
          delay={index * ANIMATION_TIMING.METRIC_STAGGER}
        />
      ))}
    </Sequence>
  );
};
