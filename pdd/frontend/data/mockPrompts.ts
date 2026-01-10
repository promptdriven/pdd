import { MockPrompt } from '../types';

export const mockPrompts: MockPrompt[] = [
  { 
    id: 'prompts/common/react-setup_TypescriptReact.prompt', 
    includes: [],
    devUnit: {
      prompt: `
# Instruction
Create a standard functional React component.

# Rules
- Use TypeScript.
- Accept a 'title' prop.
- Render the title in an h1 tag.
      `.trim(),
      code: `
import React from 'react';

type Props = {
  title: string;
};

const Component = ({ title }: Props) => {
  return (
    <div>
      <h1>{title}</h1>
    </div>
  );
};

export default Component;
      `.trim(),
      example: `
import React from 'react';
import Component from './Component';

const App = () => {
  return <Component title="Welcome!" />;
};
      `.trim(),
      test: `
import { render, screen } from '@testing-library/react';
import Component from './Component';

it('should render the title', () => {
  render(<Component title="My Title" />);
  expect(screen.getByRole('heading')).toHaveTextContent('My Title');
});
      `.trim(),
    }
  },
  { 
    id: 'prompts/common/tailwind-setup_TailwindConfig.prompt', 
    includes: [],
    devUnit: {
      prompt: `
# Instruction
Provide a basic setup for Tailwind CSS in a project.

# Content
- Include the standard tailwind.config.js file.
- Include the basic CSS file with @tailwind directives.
      `.trim(),
      code: `
// tailwind.config.js
/** @type {import('tailwindcss').Config} */
module.exports = {
  content: [
    "./src/**/*.{js,jsx,ts,tsx}",
  ],
  theme: {
    extend: {},
  },
  plugins: [],
}
      `.trim(),
      example: `
/* styles.css */
@tailwind base;
@tailwind components;
@tailwind utilities;
      `.trim(),
      test: `
// No testable code for config files.
      `.trim(),
    }
  },
  { 
    id: 'prompts/common/testing-lib_TestingLibrarySetup.prompt', 
    includes: [],
    devUnit: {
      prompt: `
# Instruction
Explain the setup for React Testing Library.

# Content
- Show necessary dependencies.
- Provide a simple test example.
      `.trim(),
      code: `
// package.json dependencies
"dependencies": {
  "@testing-library/jest-dom": "^5.16.5",
  "@testing-library/react": "^13.4.0",
  "@testing-library/user-event": "^13.5.0",
}
      `.trim(),
      example: `
// See test file for example.
      `.trim(),
      test: `
import { render, screen } from '@testing-library/react';

const Greeting = () => <h1>Hello World</h1>;

test('renders a greeting', () => {
  render(<Greeting />);
  expect(screen.getByRole('heading')).toHaveTextContent('Hello World');
});
      `.trim(),
    }
  },
  { 
    id: 'prompts/components/button_TypescriptReact.prompt', 
    includes: ['prompts/common/react-setup_TypescriptReact.prompt'],
    devUnit: {
      prompt: `
# Instruction
Create a reusable Button component.

# Imports
- prompts/common/react-setup_TypescriptReact.prompt

# Rules
- Accept standard button props (e.g., onClick, children).
- Style with Tailwind CSS.
- Have a primary blue color.
      `.trim(),
      code: `
import React from 'react';

type ButtonProps = React.ButtonHTMLAttributes<HTMLButtonElement>;

const Button: React.FC<ButtonProps> = ({ children, ...props }) => {
  return (
    <button
      className="bg-blue-500 hover:bg-blue-700 text-white font-bold py-2 px-4 rounded"
      {...props}
    >
      {children}
    </button>
  );
};

export default Button;
      `.trim(),
      example: `
import Button from './Button';

const MyComponent = () => {
  return <Button onClick={() => alert('Clicked!')}>Click Me</Button>
}
      `.trim(),
      test: `
import { render, screen } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import Button from './Button';

test('calls onClick when clicked', async () => {
  const handleClick = jest.fn();
  render(<Button onClick={handleClick}>Click</Button>);
  await userEvent.click(screen.getByText('Click'));
  expect(handleClick).toHaveBeenCalledTimes(1);
});
      `.trim(),
    }
  },
  { 
    id: 'prompts/components/modal_TypescriptReact.prompt', 
    includes: ['prompts/common/react-setup_TypescriptReact.prompt'],
    devUnit: {
      prompt: `
# Instruction
Create a basic Modal component.

# Imports
- prompts/common/react-setup_TypescriptReact.prompt

# Rules
- Show/hide based on an 'isOpen' prop.
- Have a dark overlay.
- Have a close button.
      `.trim(),
      code: `
import React from 'react';

type ModalProps = {
  isOpen: boolean;
  onClose: () => void;
  children: React.ReactNode;
};

const Modal: React.FC<ModalProps> = ({ isOpen, onClose, children }) => {
  if (!isOpen) return null;

  return (
    <div className="fixed inset-0 bg-black/50 z-50 flex items-center justify-center" onClick={onClose}>
      <div className="bg-white rounded p-8" onClick={(e) => e.stopPropagation()}>
        {children}
        <button onClick={onClose}>Close</button>
      </div>
    </div>
  );
};

export default Modal;
      `.trim(),
      example: `
const [isOpen, setIsOpen] = useState(false);

return (
  <>
    <button onClick={() => setIsOpen(true)}>Open Modal</button>
    <Modal isOpen={isOpen} onClose={() => setIsOpen(false)}>
      <p>Hello from the modal!</p>
    </Modal>
  </>
)
      `.trim(),
      test: `
import { render, screen } from '@testing-library/react';
import Modal from './Modal';

test('does not render when closed', () => {
  render(<Modal isOpen={false} onClose={() => {}}>Content</Modal>);
  expect(screen.queryByText('Content')).not.toBeInTheDocument();
});
      `.trim(),
    }
  },
  { 
    id: 'prompts/scaffold/react-spa_ReactSPA.prompt', 
    includes: [
      'prompts/common/react-setup_TypescriptReact.prompt',
      'prompts/common/tailwind-setup_TailwindConfig.prompt',
      'prompts/components/button_TypescriptReact.prompt'
    ],
    devUnit: {
      prompt: `
# Instruction
Scaffold a Single Page Application using React.

# Imports
- prompts/common/react-setup_TypescriptReact.prompt
- prompts/common/tailwind-setup_TailwindConfig.prompt
- prompts/components/button_TypescriptReact.prompt

# Rules
- Set up a basic file structure (src, components).
- Create an App component.
      `.trim(),
      code: `
// File structure:
// /src
//   /components
//     Button.tsx
//   App.tsx
//   index.css
//   index.tsx
      `.trim(),
      example: `
// src/App.tsx
import React from 'react';
import Button from './components/Button';

const App = () => {
  return (
    <div className="p-4">
      <h1 className="text-2xl">My React App</h1>
      <Button>Click me</Button>
    </div>
  )
}
      `.trim(),
      test: `
// See individual component tests.
      `.trim(),
    }
  },
  { 
    id: 'prompts/test/generate-test_ReactTest.prompt', 
    includes: ['prompts/common/testing-lib_TestingLibrarySetup.prompt', 'prompts/components/button_TypescriptReact.prompt'],
    devUnit: {
      prompt: `
# Instruction
Generate a test file for the Button component.

# Imports
- prompts/common/testing-lib_TestingLibrarySetup.prompt
- prompts/components/button_TypescriptReact.prompt

# Rules
- Use React Testing Library.
- Test the onClick handler.
      `.trim(),
      code: `
// This prompt generates a test file. See the 'test' tab for the output.
      `.trim(),
      example: `
// n/a
      `.trim(),
      test: `
import { render, screen } from '@testing-library/react';
import userEvent from '@testing-library/user-event';
import Button from '../components/Button';

test('button click handler is called', async () => {
  const onClickMock = jest.fn();
  render(<Button onClick={onClickMock}>Submit</Button>);
  const button = screen.getByRole('button', { name: /Submit/i });
  await userEvent.click(button);
  expect(onClickMock).toHaveBeenCalledTimes(1);
});
      `.trim(),
    }
  },
  { 
    id: 'prompts/full-stack-app_FullStackApp.prompt', 
    includes: ['prompts/scaffold/react-spa_ReactSPA.prompt'],
    devUnit: {
      prompt: `
# Instruction
Scaffold a full-stack application.

# Imports
- prompts/scaffold/react-spa_ReactSPA.prompt

# Backend
- Node.js with Express
- A single '/api/health' endpoint
      `.trim(),
      code: `
// server.js
const express = require('express');
const app = express();
const port = 3001;

app.get('/api/health', (req, res) => {
  res.json({ status: 'ok' });
});

app.listen(port, () => {
  console.log(\`Server listening on port \${port}\`);
});
      `.trim(),
      example: `
// To run: node server.js
// Frontend setup is inherited from react-spa.prompt
      `.trim(),
      test: `
// A supertest integration test could be written for the server.
      `.trim(),
    }
  }
];