const api = "/api/v1/observability";
const byId = (id) => document.getElementById(id);

function text(element, value) {
  element.textContent = value ?? "";
  return element;
}

function formatCost(value) {
  return `$${Number(value || 0).toFixed(4)}`;
}

function renderStats(runs) {
  const successes = runs.filter((run) => run.status === "success").length;
  const models = new Map();
  for (const run of runs) {
    if (run.model && run.model !== "unknown") models.set(run.model, (models.get(run.model) || 0) + 1);
  }
  const topModel = [...models.entries()].sort((left, right) => right[1] - left[1])[0]?.[0] || "—";
  text(byId("success-rate"), runs.length ? `${Math.round((successes / runs.length) * 100)}%` : "—");
  text(byId("total-cost"), formatCost(runs.reduce((total, run) => total + Number(run.total_cost || 0), 0)));
  text(byId("run-count"), String(runs.length));
  text(byId("top-model"), topModel);
}

function renderRuns(runs) {
  const list = byId("runs");
  list.replaceChildren();
  text(byId("run-status"), `${runs.length} recorded`);
  if (!runs.length) {
    const message = text(document.createElement("p"), "No .pdd/core_dumps reports have been recorded for this project.");
    message.classList.add("message");
    list.append(message);
    return;
  }
  for (const run of runs) {
    const button = document.createElement("button");
    button.className = "run";
    const command = text(document.createElement("span"), `pdd ${run.argv.join(" ") || "run"}`);
    command.className = "command";
    const badge = text(document.createElement("span"), run.status);
    badge.className = `badge ${run.status}`;
    const meta = text(document.createElement("span"), `${run.timestamp} · ${formatCost(run.total_cost)} · ${run.model}`);
    meta.className = "meta";
    button.append(command, badge, meta);
    button.addEventListener("click", () => loadDetail(run.filename));
    list.append(button);
  }
}

async function loadDetail(filename) {
  const details = byId("details");
  details.classList.remove("empty");
  text(details, "Loading report…");
  try {
    const response = await fetch(`${api}/runs/${encodeURIComponent(filename)}`);
    if (!response.ok) throw new Error("Run details are unavailable.");
    const report = await response.json();
    text(details, JSON.stringify(report, null, 2));
  } catch (error) {
    text(details, error instanceof Error ? error.message : "Could not load run details.");
  }
}

function renderModules(modules) {
  const container = byId("modules");
  container.replaceChildren();
  text(byId("module-count"), `${modules.length} discovered`);
  if (!modules.length) {
    const message = text(document.createElement("p"), "No .pdd/meta module reports found.");
    message.classList.add("message");
    container.append(message);
    return;
  }
  for (const module of modules) {
    const card = document.createElement("article");
    card.className = "module";
    card.append(text(document.createElement("strong"), module.module_name));
    const report = module.run_report || {};
    card.append(text(document.createElement("span"), `${module.language} · ${report.tests_passed ?? 0} passed / ${report.tests_failed ?? 0} failed`));
    container.append(card);
  }
}

async function loadDashboard() {
  text(byId("run-status"), "Loading…");
  try {
    const [runsResponse, modulesResponse] = await Promise.all([fetch(`${api}/runs`), fetch(`${api}/modules`)]);
    if (!runsResponse.ok || !modulesResponse.ok) throw new Error("Observability data is unavailable.");
    const [runs, modules] = await Promise.all([runsResponse.json(), modulesResponse.json()]);
    renderStats(runs); renderRuns(runs); renderModules(modules);
  } catch (error) {
    text(byId("run-status"), error instanceof Error ? error.message : "Could not load dashboard.");
  }
}

byId("refresh").addEventListener("click", loadDashboard);
loadDashboard();
