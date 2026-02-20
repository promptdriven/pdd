/** @type {import('next').NextConfig} */
const nextConfig = {
  // Allow large request bodies for thumbnail uploads
  experimental: {
    serverActions: {
      bodySizeLimit: '50mb',
    },
  },
};

export default nextConfig;
