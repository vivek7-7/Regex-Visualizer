import "./globals.css";

export const metadata = {
  title: "Regex Visualizer",
  description: "DFA Visualizer",
};

export default function RootLayout({ children }) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}