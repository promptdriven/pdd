
import React from 'react';
import { CommandType } from '../types';

interface TabsProps {
  activeCommand: CommandType;
  onCommandChange: (command: CommandType) => void;
}

const Tabs: React.FC<TabsProps> = ({ activeCommand, onCommandChange }) => {
  const commands = Object.values(CommandType);

  return (
    <div className="border-b border-gray-700">
      <nav className="-mb-px flex space-x-6" aria-label="Tabs">
        {commands.map((command) => (
          <button
            key={command}
            onClick={() => onCommandChange(command)}
            className={`
              whitespace-nowrap py-4 px-1 border-b-2 font-medium text-sm capitalize
              ${
                activeCommand === command
                  ? 'border-blue-500 text-blue-400'
                  : 'border-transparent text-gray-400 hover:text-gray-300 hover:border-gray-500'
              }
              focus:outline-none transition-colors duration-200
            `}
          >
            {command}
          </button>
        ))}
      </nav>
    </div>
  );
};

export default Tabs;
