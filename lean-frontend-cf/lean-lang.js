// Lean 4 syntax highlighting for CodeMirror 6
import { StreamLanguage } from '@codemirror/language';
import { tags } from '@lezer/highlight';
import { HighlightStyle, syntaxHighlighting } from '@codemirror/language';

// ── Lean 4 stream parser ──────────────────────────────
const leanMode = {
  startState() {
    return { inBlockComment: 0, inString: false };
  },

  token(stream, state) {
    // Block comments (nestable: /- ... -/)
    if (state.inBlockComment > 0) {
      while (!stream.eol()) {
        if (stream.match('/-')) {
          state.inBlockComment++;
        } else if (stream.match('-/')) {
          state.inBlockComment--;
          if (state.inBlockComment === 0) return 'blockComment';
        } else {
          stream.next();
        }
      }
      return 'blockComment';
    }

    // Start of block comment
    if (stream.match('/-')) {
      state.inBlockComment = 1;
      while (!stream.eol()) {
        if (stream.match('/-')) {
          state.inBlockComment++;
        } else if (stream.match('-/')) {
          state.inBlockComment--;
          if (state.inBlockComment === 0) return 'blockComment';
        } else {
          stream.next();
        }
      }
      return 'blockComment';
    }

    // Line comments
    if (stream.match('--')) {
      stream.skipToEnd();
      return 'lineComment';
    }

    // Strings
    if (stream.match('"')) {
      while (!stream.eol()) {
        const ch = stream.next();
        if (ch === '\\') { stream.next(); continue; }
        if (ch === '"') return 'string';
      }
      return 'string';
    }

    // Char literals
    if (stream.match(/^'[^'\\]'/)) return 'string';
    if (stream.match(/^'\\.[^']*'/)) return 'string';

    // Numbers
    if (stream.match(/^0[xX][0-9a-fA-F_]+/)) return 'number';
    if (stream.match(/^0[bB][01_]+/)) return 'number';
    if (stream.match(/^0[oO][0-7_]+/)) return 'number';
    if (stream.match(/^[0-9][0-9_]*(\.[0-9_]+)?([eE][+-]?[0-9_]+)?/)) return 'number';

    // Hash commands (#eval, #check, #print, etc.)
    if (stream.match(/^#[a-zA-Z_][a-zA-Z0-9_]*/)) return 'meta';

    // Identifiers and keywords
    if (stream.match(/^[a-zA-Z_\u03b1-\u03c9\u0391-\u03A9][a-zA-Z0-9_'\u03b1-\u03c9\u0391-\u03A9]*/)) {
      const w = stream.current();
      if (KEYWORDS.has(w)) return 'keyword';
      if (DECL_KEYWORDS.has(w)) return 'definitionKeyword';
      if (TACTIC_KEYWORDS.has(w)) return 'keyword';
      if (TYPE_KEYWORDS.has(w)) return 'typeName';
      if (BUILTIN_TYPES.has(w)) return 'typeName';
      if (LITERALS.has(w)) return 'bool';
      return 'variableName';
    }

    // Operators
    if (stream.match(/^[→←↔∀∃∧∨¬≠≤≥∈∉⊆⊂∪∩×λΣΠ⟨⟩▸·∘⁻¹]+/)) return 'operator';
    if (stream.match(/^[:=<>!&|+\-*/^%@$~?∘.]+/)) return 'operator';

    // Brackets
    if (stream.match(/^[(){}\[\]⟨⟩]/)) return 'paren';

    // Skip anything else
    stream.next();
    return null;
  },
};

const KEYWORDS = new Set([
  'if', 'then', 'else', 'match', 'with', 'do', 'let', 'have', 'show',
  'fun', 'assume', 'return', 'where', 'by', 'in', 'at', 'from',
  'open', 'import', 'export', 'namespace', 'section', 'end',
  'variable', 'universe', 'set_option', 'attribute',
  'private', 'protected', 'noncomputable', 'partial', 'unsafe',
  'mutual', 'local', 'scoped',
  'for', 'while', 'break', 'continue',
  'try', 'catch', 'finally', 'throw',
  'deriving', 'extending', 'instance', 'class',
  'sorry',
]);

const DECL_KEYWORDS = new Set([
  'def', 'theorem', 'lemma', 'example', 'abbrev',
  'structure', 'inductive', 'class', 'instance',
  'axiom', 'opaque', 'constant',
  'macro', 'macro_rules', 'syntax', 'elab', 'notation',
]);

const TACTIC_KEYWORDS = new Set([
  'intro', 'intros', 'apply', 'exact', 'rfl', 'refl',
  'simp', 'ring', 'omega', 'linarith', 'norm_num', 'decide',
  'rw', 'rewrite', 'subst', 'cases', 'induction', 'rcases', 'obtain',
  'constructor', 'left', 'right', 'exfalso', 'contradiction',
  'assumption', 'trivial', 'tauto',
  'ext', 'funext', 'congr',
  'calc', 'suffices', 'use', 'refine',
  'aesop', 'norm_cast', 'push_neg',
  'split', 'rintro', 'specialize', 'generalize',
]);

const TYPE_KEYWORDS = new Set([
  'Type', 'Prop', 'Sort',
]);

const BUILTIN_TYPES = new Set([
  'Nat', 'Int', 'Float', 'String', 'Char', 'Bool', 'Unit',
  'List', 'Array', 'Option', 'IO', 'Except',
  'True', 'False', 'And', 'Or', 'Not', 'Iff', 'Eq',
  'Fin', 'Prod', 'Sum', 'Sigma', 'Subtype',
  'StateM', 'ReaderM', 'ExceptT', 'StateT',
  'HashMap', 'HashSet', 'RBMap', 'RBSet',
]);

const LITERALS = new Set(['true', 'false']);

export const leanLanguage = StreamLanguage.define(leanMode);

// ── Lean highlight style ──────────────────────────────
export const leanHighlightStyle = syntaxHighlighting(HighlightStyle.define([
  { tag: tags.keyword, color: '#7c3aed', fontWeight: '600' },              // purple
  { tag: tags.definitionKeyword, color: '#0369a1', fontWeight: '700' },    // blue
  { tag: tags.typeName, color: '#0e7490', fontWeight: '600' },             // teal
  { tag: tags.bool, color: '#c2410c' },                                     // orange
  { tag: tags.string, color: '#15803d' },                                   // green
  { tag: tags.number, color: '#b45309' },                                   // amber
  { tag: tags.lineComment, color: '#6b7280', fontStyle: 'italic' },        // gray
  { tag: tags.blockComment, color: '#6b7280', fontStyle: 'italic' },       // gray
  { tag: tags.meta, color: '#be185d', fontWeight: '600' },                 // pink (#eval etc)
  { tag: tags.operator, color: '#64748b' },                                 // slate
  { tag: tags.paren, color: '#64748b' },
  { tag: tags.variableName, color: '#1e293b' },
]));

// Dark mode variant
export const leanHighlightStyleDark = syntaxHighlighting(HighlightStyle.define([
  { tag: tags.keyword, color: '#c084fc', fontWeight: '600' },              // purple
  { tag: tags.definitionKeyword, color: '#7dd3fc', fontWeight: '700' },    // blue
  { tag: tags.typeName, color: '#67e8f9', fontWeight: '600' },             // cyan
  { tag: tags.bool, color: '#fb923c' },                                     // orange
  { tag: tags.string, color: '#86efac' },                                   // green
  { tag: tags.number, color: '#fcd34d' },                                   // amber
  { tag: tags.lineComment, color: '#9ca3af', fontStyle: 'italic' },        // gray
  { tag: tags.blockComment, color: '#9ca3af', fontStyle: 'italic' },       // gray
  { tag: tags.meta, color: '#f9a8d4', fontWeight: '600' },                 // pink
  { tag: tags.operator, color: '#94a3b8' },                                 // slate
  { tag: tags.paren, color: '#94a3b8' },
  { tag: tags.variableName, color: '#e2e8f0' },
]));
