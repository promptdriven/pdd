// Generated from prompts/cli/release-notice.prompt.md (sha256: ec8778948e0dd9a83aef01c2ce43cd1ae49305d0a694b422805e0f92cb5b30d4).
const number = '(0|[1-9][0-9]*)';
const core = `${number}\\.${number}\\.${number}`;
const identifier = '(?:0|[1-9][0-9]*|[0-9]*[A-Za-z-][0-9A-Za-z-]*)';
const installedPattern = new RegExp(`^${core}(?:-(${identifier}(?:\\.${identifier})*))?(?:\\+[0-9A-Za-z-]+(?:\\.[0-9A-Za-z-]+)*)?$`);
const tagPattern = new RegExp(`^(?:alpha-v|v)${core}$`);
function parse(text, pattern) {
  if (typeof text !== 'string') return null;
  const match = pattern.exec(text);
  if (!match) return null;
  const parts = match.slice(1, 4).map(Number);
  return parts.every(Number.isSafeInteger) ? {parts, prerelease: Boolean(match[4])} : null;
}

// The port owns transport. No credentials, subprocesses or persistent state are needed.
async function latest() {
  const controller = new AbortController();
  let timer;
  const deadline = new Promise((_, reject) => {
    timer = setTimeout(() => { controller.abort(); reject(Error('release lookup timeout')); }, 1000);
  });
  try {
    return await Promise.race([deadline, (async () => {
      const response = await fetch('https://api.github.com/repos/promptdriven/pdd/releases/latest', {
        headers: {Accept:'application/vnd.github+json'}, credentials:'omit', redirect:'error', signal:controller.signal,
      });
      if (!response.ok) { controller.abort(); return {tag:''}; }
      const chunks = [];
      let bytes = 0;
      for await (const chunk of response.body) {
        bytes += chunk.byteLength;
        if (bytes > 65536) { controller.abort(); return {tag:''}; }
        chunks.push(chunk);
      }
      const release = JSON.parse(Buffer.concat(chunks).toString('utf8'));
      return {tag: release?.draft === false && release?.prerelease === false && typeof release?.tag_name === 'string' ? release.tag_name : ''};
    })()]);
  } catch { return {tag:''}; }
  finally { clearTimeout(timer); }
}

export async function releaseNotice({version, ci, probe}, {releases = {latest}} = {}) {
  const installed = parse(version, installedPattern);
  if (ci || probe || !installed) return {message:''};
  try {
    const {tag} = await releases.latest({});
    const available = parse(tag, tagPattern);
    if (!available) return {message:''};
    const difference = available.parts.map((value, i) => value - installed.parts[i]).find(value => value !== 0) ?? 0;
    if (difference < 0 || difference === 0 && !installed.prerelease) return {message:''};
    return {message:`pdd ${available.parts.join('.')} is available (installed ${version}). Update: npm install -g github:promptdriven/pdd#${tag}`};
  } catch { return {message:''}; }
}
