import React, { useState, useEffect } from 'react';

/**
 * DeviceIndicator - Shows current responsive breakpoint in development mode
 *
 * Only visible in development to help test responsive design across breakpoints.
 * Displays in bottom-left corner showing current breakpoint and screen width.
 */
export const DeviceIndicator: React.FC = () => {
  const [width, setWidth] = useState(window.innerWidth);

  useEffect(() => {
    const handleResize = () => setWidth(window.innerWidth);
    window.addEventListener('resize', handleResize);
    return () => window.removeEventListener('resize', handleResize);
  }, []);

  // Only show in development mode
  if (import.meta.env.PROD) return null;

  return (
    <div className="fixed bottom-2 left-2 bg-black/80 text-white text-xs px-2 py-1 rounded font-mono z-[9999] pointer-events-none">
      <span className="xs:hidden">XS (&lt;475)</span>
      <span className="hidden xs:inline sm:hidden">SM (475-640)</span>
      <span className="hidden sm:inline md:hidden">MD (640-768)</span>
      <span className="hidden md:inline lg:hidden">LG (768-1024)</span>
      <span className="hidden lg:inline xl:hidden">XL (1024-1280)</span>
      <span className="hidden xl:inline 2xl:hidden">2XL (1280-1536)</span>
      <span className="hidden 2xl:inline">2XL+ (&gt;1536)</span>
      <span className="ml-2 text-accent-400">{width}px</span>
    </div>
  );
};

export default DeviceIndicator;
