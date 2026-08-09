
import React from 'react';
import { CommandConfig } from '../types';
import InputField from './InputField';
import TextAreaField from './TextAreaField';

// Fields that should show a file browser button
const FILE_FIELDS = ['prompt', 'input-file', 'output-file', 'test-file', 'source-file', 'env-file'];

interface CommandFormProps {
  config: CommandConfig;
  formData: Record<string, string>;
  setFormData: React.Dispatch<React.SetStateAction<Record<string, string>>>;
  onBrowseFile?: (fieldName: string) => void;
}

const CommandForm: React.FC<CommandFormProps> = ({ config, formData, setFormData, onBrowseFile }) => {
  const handleChange = (e: React.ChangeEvent<HTMLInputElement | HTMLTextAreaElement>) => {
    const { name, value } = e.target;
    setFormData(prev => ({ ...prev, [name]: value }));
  };

  return (
    <div className="bg-gray-800/50 rounded-lg p-6 shadow-lg ring-1 ring-white/10">
      <div className="mb-4">
        <h2 className="text-lg font-semibold text-white capitalize">{config.name}</h2>
        <p className="text-sm text-gray-400">{config.description}</p>
      </div>
      <form className="space-y-6">
        {config.options.map(option => {
          const isFileField = FILE_FIELDS.includes(option.name);

          if (option.type === 'textarea') {
            return (
              <TextAreaField
                key={option.name}
                label={option.name}
                name={option.name}
                value={formData[option.name] || ''}
                onChange={handleChange}
                placeholder={option.placeholder}
                description={option.description}
                required={option.required}
              />
            );
          }
          return (
            <InputField
              key={option.name}
              label={option.name}
              name={option.name}
              value={formData[option.name] || ''}
              onChange={handleChange}
              placeholder={option.placeholder}
              description={option.description}
              required={option.required}
              onBrowse={isFileField && onBrowseFile ? () => onBrowseFile(option.name) : undefined}
            />
          );
        })}
      </form>
    </div>
  );
};

export default CommandForm;
