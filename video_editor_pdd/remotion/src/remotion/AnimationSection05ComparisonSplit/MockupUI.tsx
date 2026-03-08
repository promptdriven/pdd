import React from 'react';
import { COLORS, TYPOGRAPHY } from './constants';

interface MockupUIProps {
  side: 'left' | 'right';
}

export const MockupUI: React.FC<MockupUIProps> = ({ side }) => {
  const isGrayscale = side === 'left';
  const baseColor = isGrayscale ? '#64748B' : '#3B82F6';
  const textColor = isGrayscale ? '#94A3B8' : '#E2E8F0';
  const accentColor = isGrayscale ? '#475569' : '#22C55E';

  return (
    <div
      style={{
        width: '100%',
        height: '100%',
        border: `2px solid ${COLORS.mockupBorder}`,
        borderRadius: 12,
        backgroundColor: isGrayscale ? '#0F172A' : '#0A1628',
        padding: 20,
        display: 'flex',
        flexDirection: 'column',
        gap: 20,
        filter: isGrayscale ? 'grayscale(100%)' : 'none',
      }}
    >
      {/* Header Bar */}
      <div
        style={{
          width: '100%',
          height: 60,
          backgroundColor: baseColor,
          borderRadius: 8,
          display: 'flex',
          alignItems: 'center',
          padding: '0 20px',
          justifyContent: 'space-between',
        }}
      >
        <div style={{ display: 'flex', gap: 10 }}>
          <div style={{ width: 30, height: 30, borderRadius: '50%', backgroundColor: textColor }} />
          <div style={{ width: 30, height: 30, borderRadius: '50%', backgroundColor: textColor }} />
          <div style={{ width: 30, height: 30, borderRadius: '50%', backgroundColor: textColor }} />
        </div>
        <div style={{ width: 40, height: 40, borderRadius: 8, backgroundColor: accentColor }} />
      </div>

      {/* Content Grid */}
      <div
        style={{
          display: 'grid',
          gridTemplateColumns: side === 'left' ? '1fr 1fr 1fr' : '1fr 1fr',
          gap: 20,
          flex: 1,
        }}
      >
        {/* Cards */}
        {side === 'left' ? (
          <>
            {/* Cluttered layout - 6 small cards */}
            {[...Array(6)].map((_, i) => (
              <div
                key={i}
                style={{
                  backgroundColor: i % 2 === 0 ? '#1E293B' : '#334155',
                  borderRadius: 8,
                  padding: 15,
                  border: `1px solid ${COLORS.mockupBorder}`,
                  display: 'flex',
                  flexDirection: 'column',
                  gap: 10,
                }}
              >
                <div style={{ width: '80%', height: 12, backgroundColor: textColor, borderRadius: 4 }} />
                <div style={{ width: '60%', height: 8, backgroundColor: textColor, borderRadius: 4, opacity: 0.6 }} />
                <div style={{ width: '90%', height: 8, backgroundColor: textColor, borderRadius: 4, opacity: 0.6 }} />
                <div style={{ width: '40%', height: 20, backgroundColor: baseColor, borderRadius: 4, marginTop: 5 }} />
              </div>
            ))}
          </>
        ) : (
          <>
            {/* Clean layout - 2 large cards */}
            {[...Array(2)].map((_, i) => (
              <div
                key={i}
                style={{
                  backgroundColor: '#1E3A8A',
                  borderRadius: 12,
                  padding: 30,
                  border: `2px solid ${COLORS.mockupHighlight}`,
                  display: 'flex',
                  flexDirection: 'column',
                  gap: 20,
                  boxShadow: `0 4px 20px rgba(59, 130, 246, 0.3)`,
                }}
              >
                <div style={{ width: '70%', height: 20, backgroundColor: textColor, borderRadius: 6 }} />
                <div style={{ width: '90%', height: 12, backgroundColor: textColor, borderRadius: 4, opacity: 0.7 }} />
                <div style={{ width: '85%', height: 12, backgroundColor: textColor, borderRadius: 4, opacity: 0.7 }} />
                <div
                  style={{
                    width: '100%',
                    height: 100,
                    backgroundColor: accentColor,
                    borderRadius: 8,
                    marginTop: 10,
                  }}
                />
                <div
                  style={{
                    width: '50%',
                    height: 40,
                    backgroundColor: COLORS.mockupHighlight,
                    borderRadius: 8,
                    marginTop: 10,
                  }}
                />
              </div>
            ))}
          </>
        )}
      </div>

      {/* Footer - only cluttered on left */}
      {side === 'left' && (
        <div
          style={{
            width: '100%',
            height: 50,
            backgroundColor: '#334155',
            borderRadius: 8,
            display: 'flex',
            alignItems: 'center',
            padding: '0 20px',
            gap: 10,
          }}
        >
          {[...Array(5)].map((_, i) => (
            <div
              key={i}
              style={{
                width: 80,
                height: 30,
                backgroundColor: textColor,
                borderRadius: 4,
                opacity: 0.7,
              }}
            />
          ))}
        </div>
      )}
    </div>
  );
};
