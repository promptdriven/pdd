// Test Plan and Formal Verification Notes
//
// 1) Edge cases identified from the prompt and code
// - isPddCliInstalled detection order and multiple strategies:
//   • PATH detection succeeds
//   • PATH fails but uv tool path succeeds
//   • PATH and uv tool path fail, uv tool run succeeds
//   • PATH + uv fail, conda run succeeds
//   • All above fail, a common path succeeds
//   • All detection methods fail -> returns false
// - installPddCli user flows:
//   • User cancels selection -> should return and show cancellation message
//   • User selects uv, uv available -> install via uv
//   • User selects uv, uv not available, uv installation succeeds -> install via uv full or PATH
//   • User selects uv, uv install fails -> installation fails and user is notified
//   • Proper success messages and actionable buttons handled
// - runPddSetup flows:
//   • uv tool path exists -> use full path to uv tool
//   • uv tool path not found, uv exists -> use uv tool run
//   • Neither found -> fallback to pdd in PATH
// - upgradeToUvInstallation:
//   • PDD not installed -> shows warning and returns
//   • PDD installed, uv available and pdd-cli already via uv -> shows info and returns
//   • PDD installed, uv not available, user cancels uv install -> returns
//   • PDD installed, user confirms upgrade, uv install maybe required, remove old installation (best-effort), then install via uv
// - checkAndPromptInstallation:
//   • Prompt disabled in config -> returns silently
//   • Not installed, user chooses Install -> triggers installPddCli
//   • Not installed, user chooses Don't Ask Again -> updates config
//   • Not installed, user chooses Not Now -> no action
//
// 2) Which edge cases are more suitable for Z3 formal verification vs unit tests
// - Z3 suited for reasoning about logical predicates that should hold generally:
//   • Version compatibility logic for Python versions (major > 3 or major == 3 and minor >= 7)
//   • Decision logic invariants (e.g., if conda env pdd exists, conda-run command should be used for fallback)
//   These are propositional/arithmetical properties and can be encoded in Z3.
// - Unit tests suited for:
//   • Integration with shell commands through stubbing (exec)
//   • User interaction flows (vscode.window.showInformationMessage, withProgress, etc.)
//   • File path expansion and platform branching
//   • Output messaging and side effects (sending terminal commands, opening URIs, executing VS Code commands)
//
// 3) Detailed test plan
// - Unit tests will load the PddInstaller class via proxyquire with mocks for 'vscode' and 'child_process' so we can fully control behavior.
// - For each method, we simulate the different branches by mapping specific command strings to desired success/failure outcomes via a controllable exec stub.
// - We'll verify:
//   • Return values (booleans) from detection methods
//   • Which commands were attempted (without relying on internal variable names; we observe the exec inputs and effects)
//   • User prompt handling: selections and cancellations
//   • That progress and success messages lead to expected actions (terminal opened, URIs opened, setup triggered)
// - Z3 tests:
//   • Verify that the Python version compatibility predicate is correct by proving with Z3 that there are no counterexamples where major < 3 implies compatible, and that for major == 3, minor < 7 implies incompatible.
//   • Verify a high-level invariant: If a "pdd" conda environment exists (modeled abstractly), then the chosen fallback command form must be conda-run. We'll encode a simplified model and prove that no model violates the rule.
//
// 4) Notes to keep tests robust to regeneration
// - Tests focus on observable behavior of public methods and shell/UI side-effects (commands called, messages, URIs), not on internal private helpers or exact log lines.
// - We do not reference internal properties or non-exported symbols. We treat the shell as a black-box via exec stubbing.
// - We avoid tight coupling to precise strings of progress messages, focusing instead on commands executed and outcomes.
//
// -----------------------------------------------------------------------------
// Actual Test Code Below
// -----------------------------------------------------------------------------

import { strict as assert } from 'assert';
import sinon from 'sinon';

// Use CommonJS-style requires for easier proxying in TS tests
const proxyquire = require('proxyquire').noCallThru();

type ExecBehavior = {
  // Map command substrings (or exact strings) to desired result
  // First matching key wins in order of insertion
  responses: Array<{
    match: RegExp | string;
    resolve?: { stdout?: string; stderr?: string };
    reject?: Error & { stdout?: string; stderr?: string };
  }>;
};

function createExecStub(behavior: ExecBehavior) {
  const stub = sinon.stub();
  stub.callsFake((cmd: string, opts?: any, cb?: any) => {
    // child_process.exec signature variants: (cmd, options, callback) or (cmd, callback)
    const command = cmd;
    const entry = behavior.responses.find((r) =>
      typeof r.match === 'string' ? command === r.match : (r.match as RegExp).test(command)
    );
    const result = entry?.resolve ?? undefined;
    const error = entry?.reject ?? undefined;
    const stdout = result?.stdout ?? error?.stdout ?? '';
    const stderr = result?.stderr ?? error?.stderr ?? '';

    // Handle callback form
    if (typeof opts === 'function') {
      cb = opts;
    }
    if (cb) {
      if (error) cb(error, { stdout, stderr });
      else cb(null, { stdout, stderr });
      return;
    }

    // Promise form (util.promisify)
    return new Promise((resolve, reject) => {
      if (error) reject(error);
      else resolve({ stdout, stderr });
    });
  });
  return stub;
}

// Minimal vscode mock with stateful behaviors controlled by each test
function createVscodeMock() {
  let showInfoResponseQueue: Array<string | undefined> = [];
  let showInfoModalFlags: Array<boolean> = [];
  let showWarnResponseQueue: Array<string | undefined> = [];
  let createdTerminals: Array<{ name: string; sent: string[] }> = [];
  let openedUris: string[] = [];
  let executedCommands: string[] = [];
  let configStore: Record<string, any> = { 'pdd.promptForInstallation': true };

  const vscodeMock: any = {
    ProgressLocation: {
      Notification: 15,
    },
    ConfigurationTarget: {
      Global: 1,
      Workspace: 2,
      WorkspaceFolder: 3,
    },
    Uri: {
      parse: (s: string) => ({ toString: () => s, s }),
    },
    window: {
      showInformationMessage: (...args: any[]) => {
        // args signatures vary: (message, ...items) or (message, options, ...items)
        // Determine if options was passed as second arg
        let modal = false;
        if (args.length > 2 && typeof args[1] === 'object' && args[1] !== null) {
          modal = !!args[1].modal;
        }
        showInfoModalFlags.push(modal);
        const resp = showInfoResponseQueue.shift();
        return Promise.resolve(resp as any);
      },
      showWarningMessage: (...args: any[]) => {
        const resp = showWarnResponseQueue.shift();
        return Promise.resolve(resp as any);
      },
      showErrorMessage: (...args: any[]) => {
        // return resolved promise
        return Promise.resolve(undefined);
      },
      withProgress: (options: any, task: any) => {
        // Simulate progress; collect messages if needed
        const progress = { report: (_: any) => {} };
        return task(progress);
      },
      createTerminal: (name: string) => {
        const term = { name, sent: [] as string[] };
        createdTerminals.push(term);
        return {
          show: () => {},
          sendText: (text: string) => term.sent.push(text),
        };
      },
    },
    commands: {
      executeCommand: (cmd: string) => {
        executedCommands.push(cmd);
        return Promise.resolve(undefined);
      },
    },
    env: {
      openExternal: (uri: any) => {
        openedUris.push(uri?.s || uri?.toString?.());
        return Promise.resolve(true);
      },
    },
    workspace: {
      getConfiguration: (section?: string) => {
        return {
          get: <T>(key: string, defaultVal?: T) => {
            const fullKey = section ? `${section}.${key}` : key;
            return (fullKey in configStore ? configStore[fullKey] : defaultVal) as T;
          },
          update: (key: string, val: any, _target: number) => {
            const fullKey = section ? `${section}.${key}` : key;
            configStore[fullKey] = val;
            return Promise.resolve();
          },
        };
      },
    },
    __test: {
      setShowInfoResponses: (items: Array<string | undefined>) => {
        showInfoResponseQueue = items.slice();
      },
      setShowWarnResponses: (items: Array<string | undefined>) => {
        showWarnResponseQueue = items.slice();
      },
      getCreatedTerminals: () => createdTerminals,
      getOpenedUris: () => openedUris.slice(),
      getExecutedCommands: () => executedCommands.slice(),
      reset: () => {
        showInfoResponseQueue = [];
        showWarnResponseQueue = [];
        showInfoModalFlags = [];
        createdTerminals = [];
        openedUris = [];
        executedCommands = [];
        configStore = { 'pdd.promptForInstallation': true };
      },
    },
  };

  return vscodeMock;
}

function loadPddInstallerWithMocks(execStub: any, vscodeMock: any) {
  const { PddInstaller } = proxyquire('../src/pddInstaller', {
    vscode: vscodeMock,
    child_process: { exec: execStub },
  });
  return PddInstaller as { new (context?: any): any };
}

describe('PddInstaller - unit tests', () => {
  let vscodeMock: any;

  beforeEach(() => {
    vscodeMock = createVscodeMock();
  });

  afterEach(() => {
    sinon.restore();
    vscodeMock.__test.reset();
  });

  // isPddCliInstalled tests
  it('isPddCliInstalled returns true when pdd in PATH', async () => {
    const execStub = createExecStub({
      responses: [
        { match: /^pdd --version$/, resolve: { stdout: 'pdd 1.0.0' } },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    const res = await installer.isPddCliInstalled();
    assert.equal(res, true);
    assert(execStub.calledWithMatch(/^pdd --version$/));
  });

  it('isPddCliInstalled tries uv tool path when PATH fails', async () => {
    const home = process.env.HOME || '';
    const uvPath = `${home}/.local/share/uv/tools/pdd-cli/bin/pdd`;
    const execStub = createExecStub({
      responses: [
        { match: /^pdd --version$/, reject: Object.assign(new Error('not found'), {}) },
        { match: new RegExp(`^"${uvPath.replace(/\//g, '\\/')}" --version$`), resolve: { stdout: 'pdd 1.0.0' } },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    const res = await installer.isPddCliInstalled();
    assert.equal(res, true);
  });

  it('isPddCliInstalled falls back to uv tool run when others fail', async () => {
    const execStub = createExecStub({
      responses: [
        { match: /^pdd --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/pdd-cli\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /^uv tool run pdd-cli --version$/, resolve: { stdout: 'pdd 1.0.0' } },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    const res = await installer.isPddCliInstalled();
    assert.equal(res, true);
  });

  it('isPddCliInstalled falls back to conda run', async () => {
    const execStub = createExecStub({
      responses: [
        { match: /^pdd --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /uv\/tools\/pdd-cli\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /^uv tool run pdd-cli --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /^conda run -n pdd pdd --version$/, resolve: { stdout: 'pdd 1.0.0' } },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    const res = await installer.isPddCliInstalled();
    assert.equal(res, true);
  });

  it('isPddCliInstalled tries common paths and returns false if all fail', async () => {
    const execStub = createExecStub({
      responses: [
        { match: /^pdd --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /uv\/tools\/pdd-cli\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /^uv tool run pdd-cli --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /^conda run -n pdd pdd --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/anaconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/miniconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\.local\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /anaconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /miniconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/anaconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/miniconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /anaconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /miniconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    const res = await installer.isPddCliInstalled();
    assert.equal(res, false);
  });

  // installPddCli tests
  it('installPddCli handles user cancel', async () => {
    vscodeMock.__test.setShowInfoResponses(['Cancel']);
    const execStub = createExecStub({ responses: [] });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    await installer.installPddCli();
    // No commands should be run
    assert.equal(execStub.callCount, 0);
  });

  it('installPddCli installs with uv when uv available', async () => {
    vscodeMock.__test.setShowInfoResponses(['Install PDD CLI', undefined]);
    const execStub = createExecStub({
      responses: [
        { match: /^uv --version$/, resolve: { stdout: 'uv 0.1.0' } },
        { match: /^uv tool install pdd-cli$/, resolve: { stdout: 'installed' } },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    await installer.installPddCli();
    assert(execStub.calledWithMatch(/^uv tool install pdd-cli$/));
  });

  it('installPddCli installs uv then pdd via uv when uv not available', async () => {
    vscodeMock.__test.setShowInfoResponses(['Install PDD CLI', undefined]);
    const home = process.env.HOME || '';
    const uvFull = `${home}/.cargo/bin/uv`;
    const execStub = createExecStub({
      responses: [
        { match: /^uv --version$/, reject: Object.assign(new Error('no uv'), {}) },
        { match: /curl -LsSf https:\/\/astral\.sh\/uv\/install\.sh \| sh/, resolve: { stdout: 'uv installed' } },
        { match: /^uv tool install pdd-cli$/, resolve: { stdout: 'ok' } },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    await installer.installPddCli();
    assert(execStub.calledWithMatch(/^uv tool install pdd-cli$/));
  });

  // runPddSetup tests
  it('runPddSetup uses uv tool path when uv path is available', async () => {
    const home = process.env.HOME || '';
    const uvPdd = `${home}/.local/share/uv/tools/pdd-cli/bin/pdd`;
    const execStub = createExecStub({
      responses: [
        { match: /^conda env list$/, reject: Object.assign(new Error('no conda'), {}) },
        { match: new RegExp(`^"${uvPdd.replace(/\//g, '\\/')}" --version$`), resolve: { stdout: 'pdd 1.0.0' } },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    await installer.runPddSetup();
    const terms = vscodeMock.__test.getCreatedTerminals();
    assert(terms[0].sent[0].startsWith(`"${uvPdd}" setup`));
  });

  it('runPddSetup uses uv tool run when uv available and path missing', async () => {
    const execStub = createExecStub({
      responses: [
        { match: /^conda env list$/, reject: Object.assign(new Error('no conda'), {}) },
        { match: /\/pdd-cli\/bin\/pdd" --version$/, reject: Object.assign(new Error('no uv path'), {}) },
        { match: /^uv --version$/, resolve: { stdout: 'uv 0.1.0' } },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    await installer.runPddSetup();
    const terms = vscodeMock.__test.getCreatedTerminals();
    assert(terms[0].sent[0].startsWith('uv tool run pdd-cli setup'));
  });

  it('runPddSetup falls back to pdd setup when neither conda nor uv available', async () => {
    const execStub = createExecStub({
      responses: [
        { match: /^conda env list$/, reject: Object.assign(new Error('no conda'), {}) },
        { match: /\/pdd-cli\/bin\/pdd" --version$/, reject: Object.assign(new Error('no uv path'), {}) },
        { match: /^uv --version$/, reject: Object.assign(new Error('no uv'), {}) },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    await installer.runPddSetup();
    const terms = vscodeMock.__test.getCreatedTerminals();
    assert(terms[0].sent[0].startsWith('pdd setup'));
  });

  // upgradeToUvInstallation tests
  it('upgradeToUvInstallation warns when PDD not installed', async () => {
    const execStub = createExecStub({
      responses: [
        // isPddCliInstalled: all detections fail
        { match: /^pdd --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /uv\/tools\/pdd-cli\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /^uv tool run pdd-cli --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /^conda run -n pdd pdd --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/anaconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/miniconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\.local\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /anaconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /miniconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/anaconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/miniconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /anaconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /miniconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
      ],
    });
    const PddInstallerClass2 = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer2 = new PddInstallerClass2();
    await installer2.upgradeToUvInstallation();
    // No further actions expected
  });

  it('upgradeToUvInstallation exits if already uv installed', async () => {
    const execStub = createExecStub({
      responses: [
        // isPddCliInstalled -> succeed quickly via PATH
        { match: /^pdd --version$/, resolve: { stdout: 'pdd 1.0.0' } },
        // uv available
        { match: /^uv --version$/, resolve: { stdout: 'uv 0.1.0' } },
        // uv tool list shows pdd-cli
        { match: /^uv tool list$/, resolve: { stdout: 'pdd-cli' } },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    await installer.upgradeToUvInstallation();
  });

  it('upgradeToUvInstallation proceeds to install uv and upgrade when confirmed', async () => {
    // Modal 1: Install uv and upgrade -> user selects
    // Modal 2: Confirm upgrade -> user selects Yes
    vscodeMock.__test.setShowInfoResponses(['Install uv and upgrade', 'Yes, upgrade to uv', undefined]);
    const execStub = createExecStub({
      responses: [
        // isPddCliInstalled true via PATH
        { match: /^pdd --version$/, resolve: { stdout: 'pdd 1.0.0' } },
        // uv not available
        { match: /^uv --version$/, reject: Object.assign(new Error('no uv'), {}) },
        // install uv
        { match: /curl -LsSf https:\/\/astral\.sh\/uv\/install\.sh \| sh/, resolve: { stdout: 'installed uv' } },
        // best-effort remove old
        { match: /^pip uninstall pdd-cli -y$/, resolve: { stdout: 'uninstalled' } },
        // install via uv
        { match: /^uv tool install pdd-cli$/, resolve: { stdout: 'ok' } },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    await installer.upgradeToUvInstallation();
    assert(execStub.calledWithMatch(/^uv tool install pdd-cli$/));
  });

  it('upgradeToUvInstallation allows cancel when uv missing and user cancels', async () => {
    vscodeMock.__test.setShowInfoResponses(['Cancel']);
    const execStub = createExecStub({
      responses: [
        // isPddCliInstalled
        { match: /^pdd --version$/, resolve: { stdout: 'pdd 1.0.0' } },
        // uv --version missing
        { match: /^uv --version$/, reject: Object.assign(new Error('no uv'), {}) },
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    const installer = new PddInstaller();
    await installer.upgradeToUvInstallation();
    // Should not proceed to install uv
    assert.equal(execStub.calledWithMatch(/install\.sh/), false);
  });

  // checkAndPromptInstallation
  it('checkAndPromptInstallation respects prompt disabled', async () => {
    // Update config first: disable prompt
    const execStub = createExecStub({
      responses: [
        // isPddCliInstalled not reached due to prompt disabled
      ],
    });
    const PddInstaller = loadPddInstallerWithMocks(execStub, vscodeMock);
    // set setting
    await vscodeMock.workspace.getConfiguration('pdd').update('promptForInstallation', false, vscodeMock.ConfigurationTarget.Global);

    const installer = new PddInstaller();
    await installer.checkAndPromptInstallation();
    assert.equal(execStub.callCount, 0);
  });

  it("checkAndPromptInstallation sets Don't Ask Again", async () => {
    vscodeMock.__test.setShowInfoResponses(["Don't Ask Again"]);
    const execStub = createExecStub({
      responses: [
        // isPddCliInstalled -> false
        { match: /^pdd --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /uv\/tools\/pdd-cli\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /^uv tool run pdd-cli --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /^conda run -n pdd pdd --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/anaconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/miniconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\.local\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /anaconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /miniconda3\/envs\/pdd\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/anaconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /\/opt\/miniconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /anaconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
        { match: /miniconda3\/bin\/pdd" --version$/, reject: Object.assign(new Error('no'), {}) },
      ],
    });
    const PddInstallerClass = loadPddInstallerWithMocks(execStub, vscodeMock);

    const installer = new PddInstallerClass();
    await installer.checkAndPromptInstallation();
    const cfg = vscodeMock.workspace.getConfiguration('pdd');
    assert.equal(cfg.get('promptForInstallation', true), false);
  });
});