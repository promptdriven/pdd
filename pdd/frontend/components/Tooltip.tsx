import React from 'react';

interface TooltipProps {
  content: React.ReactNode;
  children: React.ReactNode;
}

const Tooltip: React.FC<TooltipProps> = ({ content, children }) => {
  return (
    <div className="relative group flex items-center">
      {children}
      <div className="absolute top-full mt-2 w-max max-w-xs bg-gray-900 text-white text-xs rounded-md py-1.5 px-3 opacity-0 group-hover:opacity-100 transition-opacity duration-200 pointer-events-none z-50 ring-1 ring-white/10 shadow-lg">
        {content}
      </div>
    </div>
  );
};

export default Tooltip;
