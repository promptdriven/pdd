// Generated from prompts/cli/release-notice.prompt.md.
const pattern = /^(?:alpha-v|v)?(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)$/;

async function latestRelease() {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), 1000);
  try {
    const response = await fetch('https://api.github.com/repos/promptdriven/pdd/releases/latest', {
      headers: { 'User-Agent': 'pdd', Accept: 'application/vnd.github+json' },
      signal: controller.signal,
      redirect: 'error'
    });
    if (!response.ok) return { tag: '' };
    const body = await response.json();
    return { tag: body && typeof body.tag_name === 'string' ? body.tag_name : '' };
  } finally { clearTimeout(timer); }
}

export async function releaseNotice({ version, ci }, ports = {}) {
  if (ci) return { notice: '' };
  try {
    const installed = pattern.exec(version);
    const { tag } = await (ports.latest || latestRelease)();
    const latest = typeof tag === 'string' && pattern.exec(tag);
    if (!installed || !latest) return { notice: '' };
    const a = installed.slice(1).map(BigInt);
    const b = latest.slice(1).map(BigInt);
    let newer = false;
    for (let i = 0; i < 3; i++) {
      if (a[i] !== b[i]) { newer = b[i] > a[i]; break; }
    }
    return { notice: newer ? `pdd ${installed.slice(1).join('.')}: update available (${latest.slice(1).join('.')}). Run: npm install -g github:promptdriven/pdd\n` : '' };
  } catch { return { notice: '' }; }
}
