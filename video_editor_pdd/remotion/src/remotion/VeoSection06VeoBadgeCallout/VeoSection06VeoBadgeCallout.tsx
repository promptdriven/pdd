import React from 'react';
import { AbsoluteFill } from 'remotion';
import { BadgePill } from './BadgePill';

export const VeoSection06VeoBadgeCallout: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: 'transparent',
      }}
    >
      <BadgePill />
    </AbsoluteFill>
  );
};

export const defaultVeoSection06VeoBadgeCalloutProps = {};

export default VeoSection06VeoBadgeCallout;
