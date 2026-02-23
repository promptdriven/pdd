import type { Metadata } from 'next';
import './globals.css';

export const metadata: Metadata = {
  title: 'Video Pipeline Editor',
  description: 'AI-powered video production pipeline',
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en" className="dark">
      <body className="bg-panel text-slate-200 antialiased">
        <main className="h-screen overflow-hidden">{children}</main>
      </body>
    </html>
  );
}