// ── Config ────────────────────────────────────────────
const API_BASE = 'https://lean4-servers.xuanji.workers.dev';
const VERSIONS = [
  { id: 'lean-4-24-0', label: '4.24' },
  { id: 'lean-4-25-0', label: '4.25' },
  { id: 'lean-4-26-0', label: '4.26' },
  { id: 'lean-4-27-0', label: '4.27' },
  { id: 'lean-4-28-0-rc1', label: '4.28-rc1' },
];

const EXAMPLES = [
  {
    name: 'Hello Lean',
    code: `-- Welcome to Lean 4 Editor
-- Press Ctrl+Enter or click ▶ Run to evaluate

#eval "Hello, Lean! 🎉"

#eval 2 + 3

#check Nat.add_comm

theorem add_zero (n : Nat) : n + 0 = n := by
  simp
`,
  },
  {
    name: 'Lists & Tactics',
    code: `-- Working with lists and proving properties

def myReverse : List α → List α
  | [] => []
  | x :: xs => myReverse xs ++ [x]

#eval myReverse [1, 2, 3, 4, 5]

#eval [1, 2, 3].map (· * 10)

#eval [1, 2, 3, 4, 5].filter (· > 3)

-- Reversing a singleton is itself
theorem reverse_singleton (x : α) : myReverse [x] = [x] := by
  simp [myReverse]

-- Reverse distributes over append (reversed)
theorem reverse_append (xs ys : List α) :
    myReverse (xs ++ ys) = myReverse ys ++ myReverse xs := by
  induction xs with
  | nil => simp [myReverse]
  | cons x xs ih => simp [myReverse, ih, List.append_assoc]

-- Reverse is an involution
theorem reverse_reverse (xs : List α) :
    myReverse (myReverse xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [myReverse, reverse_append, ih]

-- Length is preserved by reverse
theorem reverse_length (xs : List α) :
    (myReverse xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [myReverse, ih]

#eval myReverse (myReverse [1, 2, 3, 4, 5])
`,
  },
  {
    name: 'NNG Challenges',
    code: `-- Natural Number Game challenges (proofs left as sorry)
-- From github.com/chasenorman/Canonical
-- Try replacing sorry with actual proofs!

-- TUTORIAL WORLD

example (x q : Nat) : (37 * x) + q = (37 * x) + q := by sorry

example (x y : Nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by sorry

example : 2 = Nat.succ (Nat.succ 0) := by sorry

example (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by sorry

example (n : Nat) : Nat.succ n = n + 1 := by sorry

example : 2 + 2 = 4 := by sorry

-- ADDITION WORLD

theorem zero_add (n : Nat) : 0 + n = n := by sorry

theorem succ_add (a b : Nat) : a.succ + b = (a + b).succ := by sorry

theorem add_comm (a b : Nat) : a + b = b + a := by sorry

theorem add_assoc (a b c : Nat) : a + b + c = a + (b + c) := by sorry

theorem add_right_comm (a b c : Nat) : a + b + c = a + c + b := by sorry

-- IMPLICATION WORLD

example (x y z : Nat) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by sorry

example (x y : Nat) (h : 0 + x = 0 + y + 2) : x = y + 2 := by sorry

example (x y : Nat) (h1 : x = 37) (h2 : x = 37 \u2192 y = 42) : y = 42 := by sorry

example (x : Nat) (h : x + 1 = 4) : x = 3 := by sorry

example (x : Nat) : x = 37 \u2192 x = 37 := by sorry

example (x y : Nat) : x + 1 = y + 1 \u2192 x = y := by sorry

example (x y : Nat) (h1 : x = y) (h2 : x \u2260 y) : False := by sorry

example : 0 \u2260 1 := by sorry

example : 1 \u2260 0 := by sorry

example : 2 + 2 \u2260 5 := by sorry

-- MULTIPLICATION WORLD

theorem mul_one (m : Nat) : m * 1 = m := by sorry

theorem zero_mul (m : Nat) : 0 * m = 0 := by sorry

theorem succ_mul (a b : Nat) : a.succ * b = a * b + b := by sorry

theorem mul_comm (a b : Nat) : a * b = b * a := by sorry

theorem one_mul (m : Nat) : 1 * m = m := by sorry

theorem two_mul (m : Nat) : 2 * m = m + m := by sorry

theorem mul_add (a b c : Nat) : a * (b + c) = a * b + a * c := by sorry

theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by sorry

theorem mul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by sorry

-- ALGORITHM WORLD

theorem add_left_comm (a b c : Nat) : a + (b + c) = b + (a + c) := by sorry

example (a b c d : Nat) : (a + b) + (c + d) = ((a + c) + d) + b := by sorry

example (a b c d e f g h : Nat) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := sorry

-- ADVANCED ADDITION WORLD

theorem add_right_cancel (a b n : Nat) : a + n = b + n \u2192 a = b := by sorry

theorem add_left_cancel (a b n : Nat) : n + a = n + b \u2192 a = b := by sorry

theorem add_left_eq_self (x y : Nat) : x + y = y \u2192 x = 0 := by sorry

theorem add_right_eq_self (x y : Nat) : x + y = x \u2192 y = 0 := by sorry

theorem add_right_eq_zero (a b : Nat) : a + b = 0 \u2192 a = 0 := by sorry

theorem add_left_eq_zero (a b : Nat) : a + b = 0 \u2192 b = 0 := by sorry

-- POWER WORLD

example : 0^0 = 1 := by sorry

example (n : Nat) : 0^n.succ = 0 := by sorry

theorem pow_one (a : Nat) : a^1 = a := by sorry

theorem one_pow (n : Nat) : 1^n = 1 := sorry

theorem pow_two (a : Nat) : a^2 = a * a := by sorry

theorem pow_add (a m n : Nat) : a^(m + n) = a^m * a^n := by sorry

theorem mul_pow (a b n : Nat) : (a * b)^n = a^n * b^n := sorry

theorem pow_pow (a m n : Nat) : (a^m)^n = a^(m * n) := by sorry

theorem add_sq (a b : Nat) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := sorry

-- LEQ WORLD

example (x : Nat) : x \u2264 x := by sorry

theorem zero_le (x : Nat) : 0 \u2264 x := by sorry

example (x : Nat) : x \u2264 x.succ := by sorry

theorem le_trans (x y z : Nat) : x \u2264 y \u2192 y \u2264 z \u2192 x \u2264 z := by sorry

theorem le_zero (x : Nat) : x \u2264 0 \u2192 x = 0 := by sorry

theorem le_antisymm (x y : Nat) : x \u2264 y \u2192 y \u2264 x \u2192 x = y := sorry

example (x y : Nat) (h : x = 37 \u2228 y = 42) : y = 42 \u2228 x = 37 := by sorry

theorem le_total (x y : Nat) : x \u2264 y \u2228 y \u2264 x := sorry

-- ADVANCED MULTIPLICATION WORLD

theorem mul_le_mul_right (a b t : Nat) (h : a \u2264 b) : a * t \u2264 b * t := by sorry

theorem mul_left_ne_zero (a b : Nat) (h : a * b \u2260 0) : b \u2260 0 := by sorry

theorem eq_succ_of_ne_zero (a : Nat) (ha : a \u2260 0) : \u2203 n, a = Nat.succ n := by sorry

theorem one_le_of_ne_zero (a : Nat) (ha : a \u2260 0) : 1 \u2264 a := by sorry

theorem le_mul_right (a b : Nat) (h : a * b \u2260 0) : a \u2264 (a * b) := sorry

theorem mul_right_eq_one (x y : Nat) (h : x * y = 1) : x = 1 := sorry

theorem mul_ne_zero (a b : Nat) (ha : a \u2260 0) (hb : b \u2260 0) : a * b \u2260 0 := sorry

theorem mul_eq_zero (a b : Nat) (h : a * b = 0) : a = 0 \u2228 b = 0 := by sorry

theorem mul_left_cancel (a b c : Nat) (ha : a \u2260 0) (h : a * b = a * c) : b = c := sorry

theorem mul_right_eq_self (a b : Nat) (ha : a \u2260 0) (h : a * b = a) : b = 1 := by sorry
`,
  },
];

const DEFAULT_CODE = EXAMPLES[0].code;

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

// ── Examples menu ──────────────────────────────────────
const examplesBtn = document.getElementById('examples-btn');
const examplesMenu = document.getElementById('examples-menu');

EXAMPLES.forEach((ex, i) => {
  const item = document.createElement('button');
  item.textContent = ex.name;
  item.addEventListener('click', () => {
    textarea.value = ex.code;
    examplesMenu.classList.add('hidden');
  });
  examplesMenu.appendChild(item);
});

examplesBtn.addEventListener('click', (e) => {
  e.stopPropagation();
  examplesMenu.classList.toggle('hidden');
});

document.addEventListener('click', () => {
  examplesMenu.classList.add('hidden');
});

examplesMenu.addEventListener('click', (e) => e.stopPropagation());

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
