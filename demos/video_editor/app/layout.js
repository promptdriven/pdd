import './globals.css';

export const metadata = {
  title: 'AI Video Editor',
  description: 'AI-First Video Editor — human as director, AI as crew',
};

export default function RootLayout({ children }) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
