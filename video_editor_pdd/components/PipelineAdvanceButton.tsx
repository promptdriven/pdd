'use client';

import React from 'react';

type PipelineAdvanceButtonProps = {
  onClick?: () => void;
  disabled?: boolean;
  label?: string;
  className?: string;
};

export default function PipelineAdvanceButton({
  onClick,
  disabled = false,
  label = 'Continue →',
  className = '',
}: PipelineAdvanceButtonProps) {
  return (
    <button
      type="button"
      onClick={onClick}
      disabled={disabled}
      className={`rounded-md bg-emerald-600 px-4 py-2 text-sm font-semibold text-white transition hover:bg-emerald-700 disabled:cursor-not-allowed disabled:bg-slate-700 disabled:text-slate-500 ${className}`.trim()}
    >
      {label}
    </button>
  );
}
