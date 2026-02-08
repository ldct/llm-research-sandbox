// ── Config ────────────────────────────────────────────
const API_BASE = 'https://lean4-servers.xuanji.workers.dev';
const VERSIONS = [
  { id: 'lean-4-24-0', label: '4.24' },
  { id: 'lean-4-25-0', label: '4.25' },
  { id: 'lean-4-26-0', label: '4.26' },
  { id: 'lean-4-27-0', label: '4.27' },
  { id: 'lean-4-28-0-rc1', label: '4.28-rc1' },
];

const DEFAULT_CODE = `-- Welcome to Lean 4 Editor
-- Press Ctrl+Enter or click ▶ Run to evaluate

#eval "Hello, Lean! 🎉"

#eval 2 + 3

#check Nat.add_comm

theorem add_zero (n : Nat) : n + 0 = n := by
  simp
`;

// ── State ─────────────────────────────────────────────
let currentVersion = localStorage.getItem('lean-version') || 'lean-4-27-0';
let running = false;

// ── DOM refs ──────────────────────────────────────────
const editorPane = document.getElementById('editor-pane');
const outputContent = document.getElementById('output-content');
const runBtn = document.getElementById('run-btn');
const statusVersion = document.getElementById('status-version');
const statusElapsed = document.getElementById('status-elapsed');
const statusState = document.getElementById('status-state');
const divider = document.getElementById('divider');

// ── Editor setup (plain textarea) ─────────────────────
const textarea = document.createElement('textarea');
textarea.id = 'code-input';
textarea.spellcheck = false;
textarea.autocomplete = 'off';
textarea.value = DEFAULT_CODE;
editorPane.appendChild(textarea);

textarea.addEventListener('keydown', (e) => {
  if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
    e.preventDefault();
    runCode();
  }
  // Tab inserts 2 spaces
  if (e.key === 'Tab') {
    e.preventDefault();
    const start = textarea.selectionStart;
    const end = textarea.selectionEnd;
    textarea.value = textarea.value.substring(0, start) + '  ' + textarea.value.substring(end);
    textarea.selectionStart = textarea.selectionEnd = start + 2;
  }
});

// ── Version toggle ────────────────────────────────────
function setVersion(v) {
  currentVersion = v;
  localStorage.setItem('lean-version', v);
  document.querySelectorAll('#version-toggle button').forEach(btn => {
    btn.classList.toggle('active', btn.dataset.version === v);
  });
  const vObj = VERSIONS.find(x => x.id === v);
  statusVersion.textContent = `Lean ${vObj ? vObj.label : v}`;
}

document.getElementById('version-toggle').addEventListener('click', (e) => {
  const btn = e.target.closest('button[data-version]');
  if (btn) setVersion(btn.dataset.version);
});

setVersion(currentVersion);

// ── Run code ──────────────────────────────────────────
async function runCode() {
  if (running) return;
  running = true;

  const code = textarea.value;
  const url = `${API_BASE}/${currentVersion}`;

  // UI: loading
  runBtn.disabled = true;
  runBtn.querySelector('.run-icon').classList.add('hidden');
  runBtn.querySelector('.run-label').textContent = 'Running…';
  runBtn.querySelector('.spinner').classList.remove('hidden');
  document.body.classList.add('running');
  statusState.textContent = 'Running…';
  statusElapsed.textContent = '';
  outputContent.innerHTML = '<div class="output-placeholder">Evaluating…</div>';

  const t0 = performance.now();

  try {
    const resp = await fetch(url, {
      method: 'POST',
      body: code,
    });

    const wallMs = performance.now() - t0;

    if (!resp.ok) {
      throw new Error(`HTTP ${resp.status}: ${await resp.text()}`);
    }

    const data = await resp.json();
    renderOutput(data, wallMs);
    statusState.textContent = data.ok ? 'Success' : 'Error';
    statusElapsed.textContent = `${data.elapsed.toFixed(2)}s (wall: ${(wallMs / 1000).toFixed(2)}s)`;
  } catch (err) {
    outputContent.innerHTML = `<div class="output-error-msg">${escHtml(err.message)}</div>`;
    statusState.textContent = 'Error';
    const wallMs = performance.now() - t0;
    statusElapsed.textContent = `wall: ${(wallMs / 1000).toFixed(2)}s`;
  } finally {
    running = false;
    runBtn.disabled = false;
    runBtn.querySelector('.run-icon').classList.remove('hidden');
    runBtn.querySelector('.run-label').textContent = 'Run';
    runBtn.querySelector('.spinner').classList.add('hidden');
    document.body.classList.remove('running');
  }
}

runBtn.addEventListener('click', runCode);

// ── Render output ─────────────────────────────────────
function renderOutput(data, wallMs) {
  let html = '';

  if (data.stdout && data.stdout.trim()) {
    html += `
      <div class="output-section stdout">
        <div class="output-section-label">stdout</div>
        <pre>${formatOutputText(data.stdout)}</pre>
      </div>`;
  }

  if (data.stderr && data.stderr.trim()) {
    html += `
      <div class="output-section stderr">
        <div class="output-section-label">stderr</div>
        <pre>${formatOutputText(data.stderr)}</pre>
      </div>`;
  }

  if (!data.stdout?.trim() && !data.stderr?.trim()) {
    html += '<div class="output-placeholder">No output.</div>';
  }

  const exitClass = data.exitCode === 0 ? 'exit-ok' : 'exit-fail';
  html += `
    <div class="output-meta">
      <span class="${exitClass}">exit: ${data.exitCode}</span>
      <span>lean: ${data.elapsed.toFixed(2)}s</span>
      <span>wall: ${(wallMs / 1000).toFixed(2)}s</span>
    </div>`;

  outputContent.innerHTML = html;

  // Attach click handlers for line links
  outputContent.querySelectorAll('.error-line-link').forEach(el => {
    el.addEventListener('click', () => {
      const line = parseInt(el.dataset.line, 10);
      jumpToLine(line);
    });
  });
}

function formatOutputText(text) {
  const escaped = escHtml(text);
  return escaped.replace(
    /(?:&lt;stdin&gt;)?(:(\d+):(\d+):)/g,
    (match, full, line, col) => {
      return `<span class="error-line-link" data-line="${line}" data-col="${col}">${full}</span>`;
    }
  );
}

function jumpToLine(line) {
  const lines = textarea.value.split('\n');
  let pos = 0;
  for (let i = 0; i < Math.min(line - 1, lines.length); i++) {
    pos += lines[i].length + 1;
  }
  textarea.focus();
  textarea.selectionStart = textarea.selectionEnd = pos;
}

function escHtml(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

// ── Resizable divider ─────────────────────────────────
let dragging = false;

divider.addEventListener('mousedown', (e) => {
  dragging = true;
  divider.classList.add('dragging');
  e.preventDefault();
});

window.addEventListener('mousemove', (e) => {
  if (!dragging) return;
  const main = document.getElementById('main');
  const rect = main.getBoundingClientRect();
  const pct = ((e.clientX - rect.left) / rect.width) * 100;
  const clamped = Math.max(20, Math.min(80, pct));
  editorPane.style.flex = `0 0 ${clamped}%`;
  document.getElementById('output-pane').style.flex = `0 0 ${100 - clamped}%`;
});

window.addEventListener('mouseup', () => {
  if (dragging) {
    dragging = false;
    divider.classList.remove('dragging');
  }
});
