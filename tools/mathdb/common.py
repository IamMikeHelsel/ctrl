"""Shared helpers for the mathdb build/query/eval scripts.

Only the Python standard library and numpy are needed here, so query.py runs
under the system python3.  The optional dense retriever (WordLlama) is loaded
lazily and is skipped if the package is not importable.
"""
from __future__ import annotations

import hashlib
import os
import re
import unicodedata
import zlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
_CACHE = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache")) / "ctrl-mathdb"
DEFAULT_INDEX = Path(os.environ.get("MATHDB_INDEX", _CACHE / "index"))
DEFAULT_CORPORA = Path(os.environ.get("MATHDB_CORPORA", _CACHE / "corpora"))

# --------------------------------------------------------------------------
# Unicode math symbols -> words.  Applied to statement text so that natural
# language queries ("sum over", "integral", "divides") reach symbolic Lean.
SYMBOL_WORDS = {
    "∑": "sum", "∏": "product prod", "∫": "integral", "∮": "integral contour",
    "≤": "le", "≥": "ge", "<": "lt", ">": "gt", "≠": "ne", "∣": "dvd divides",
    "∈": "mem", "∉": "notmem", "⊆": "subset", "⊂": "ssubset", "⊇": "superset",
    "∩": "inter intersection", "∪": "union", "⋃": "iunion union", "⋂": "iinter intersection",
    "∀": "forall", "∃": "exists", "∃!": "existsunique", "¬": "not", "∧": "and",
    "∨": "or", "→": "imp", "↔": "iff", "ℕ": "nat natural", "ℤ": "int integer",
    "ℚ": "rat rational", "ℝ": "real", "ℂ": "complex", "ℍ": "quaternion upperhalfplane",
    "√": "sqrt", "‖": "norm", "⁻¹": "inv inverse", "∘": "comp", "π": "pi",
    "∞": "infinity top", "⊤": "top", "⊥": "bot", "∅": "empty", "×": "prod",
    "•": "smul", "⬝": "dot", "ᵀ": "transpose", "†": "adjoint", "∂": "partial deriv",
    "∇": "grad", "≃": "equiv", "≅": "iso", "≈": "approx", "∼": "sim",
    "⊗": "tensor", "⊕": "sum direct", "∗": "star", "⋆": "star", "ε": "epsilon",
    "δ": "delta", "⌊": "floor", "⌈": "ceil", "∆": "symmdiff", "∆ ": "symmdiff",
    "ᶜ": "compl complement", "⟂": "orthogonal perp", "∠": "angle", "°": "degree",
    "ζ": "zeta", "Γ": "gamma", "φ": "phi totient", "μ": "mu measure", "σ": "sigma",
    "ω": "omega", "∡": "angle", "⧸": "quotient", "≡": "modeq congruent",
    "∑'": "tsum sum", "𝓝": "nhds neighborhood", "⇑": "coe", "↑": "coe cast",
}

# Lean naming-convention abbreviations -> words (applied to declaration names).
NAME_WORDS = {
    "lt": "less", "le": "less equal", "gt": "greater", "ge": "greater equal",
    "ne": "not equal", "eq": "equal", "iff": "iff equivalent", "mul": "multiplication product",
    "add": "addition sum", "sub": "subtraction", "div": "division", "pow": "power",
    "sq": "square", "sqrt": "square root", "abs": "absolute value", "inv": "inverse",
    "neg": "negative negation", "pos": "positive", "nonneg": "nonnegative", "nonpos": "nonpositive",
    "deriv": "derivative", "fderiv": "derivative frechet", "integral": "integral",
    "card": "cardinality", "dvd": "divides divisibility", "gcd": "gcd greatest common divisor",
    "lcm": "lcm least common multiple", "mem": "member", "inj": "injective",
    "surj": "surjective", "bij": "bijective", "cont": "continuous", "tendsto": "limit converges tendsto",
    "nat": "natural", "int": "integer", "rat": "rational", "zmod": "integers modulo",
    "finset": "finite set", "fintype": "finite type", "det": "determinant", "tr": "trace",
    "exp": "exponential", "log": "logarithm", "sin": "sine", "cos": "cosine",
    "mono": "monotone", "anti": "antitone", "succ": "successor", "pred": "predecessor",
    "dist": "distance", "nhds": "neighborhood", "ae": "almost everywhere", "lintegral": "lebesgue integral",
    "comp": "composition", "id": "identity", "symm": "symmetric", "trans": "transitive",
    "refl": "reflexive", "irrefl": "irreflexive", "zpow": "integer power", "npow": "power",
    "nsmul": "scalar multiple", "smul": "scalar multiplication", "prod": "product",
    "sum": "sum", "tsum": "infinite sum series", "summable": "summable convergent series",
    "dare": "discrete algebraic riccati equation", "care": "continuous algebraic riccati equation",
    "lqr": "linear quadratic regulator", "lqg": "linear quadratic gaussian", "psd": "positive semidefinite",
    "posdef": "positive definite", "hinf": "h infinity", "iss": "input to state stability",
    "clf": "control lyapunov function", "cbf": "control barrier function", "mpc": "model predictive control",
    "ekf": "extended kalman filter", "ukf": "unscented kalman filter", "kf": "kalman filter",
}

_CAMEL = re.compile(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+|[^\W\d_]+", re.U)
_WORD = re.compile(r"[\w']+", re.U)
_STOP = frozenset("a an the of to in on for is are be by with as at and or that this it its from".split())


def sym_token(ch: str) -> str:
    """Encode a non-alphanumeric symbol as an FTS-safe token, e.g. ∑ -> u2211."""
    return "u%x" % ord(ch)


def split_ident(name: str):
    """Split a Lean identifier into lowercase subwords.

    `Nat.exists_infinite_primes` -> nat exists infinite primes
    `IsSumDistinctSet`           -> is sum distinct set
    `dare_unique_of_detectable`  -> dare unique of detectable
    """
    out = []
    for part in re.split(r"[._\s'!?«»]+", name):
        if not part:
            continue
        for w in _CAMEL.findall(part):
            out.append(w.lower())
    return out


def humanize_name(name: str) -> str:
    words = split_ident(name)
    exp = []
    for w in words:
        exp.append(w)
        if w in NAME_WORDS and NAME_WORDS[w] != w:
            exp.append(NAME_WORDS[w])
    return " ".join(exp)


_LATEX_CMD = re.compile(r"\\([A-Za-z]+)")


def tokenize(text: str, expand_symbols: bool = True):
    """Identifier-aware tokenizer used for BM25 (both index and query side).

    - splits camelCase / snake_case / dotted names into subwords and also keeps
      the lowercase compound word when it had internal structure;
    - turns LaTeX commands (\\sum, \\mathbb) into words;
    - keeps unicode math symbols, encoded as u<hex> tokens, plus (optionally)
      their English names from SYMBOL_WORDS.
    """
    if not text:
        return []
    toks = []
    text = _LATEX_CMD.sub(lambda m: " " + m.group(1) + " ", text)
    for m in re.finditer(r"\w[\w'.]*|[^\w\s]", text, re.U):
        t = m.group(0)
        if t[0].isalnum() or t[0] == "_":
            parts = split_ident(t)
            toks.extend(p for p in parts if p not in _STOP)
            flat = re.sub(r"[\W_]", "", t).lower()
            if len(parts) > 1 and len(flat) <= 40:
                toks.append(flat)
            if expand_symbols:
                for ch in t:
                    if ord(ch) > 127 and ch in SYMBOL_WORDS:
                        toks.extend(SYMBOL_WORDS[ch].split())
        else:
            if t in "()[]{},.:;'\"`$\\=-+*/|^_~#@&%!?":
                continue
            if unicodedata.category(t)[0] in "SP" or ord(t) > 127:
                toks.append(sym_token(t))
                if expand_symbols and t in SYMBOL_WORDS:
                    toks.extend(SYMBOL_WORDS[t].split())
    return toks


def char_ngrams(text: str, nmin: int = 3, nmax: int = 5):
    """Word-boundary char n-grams (like sklearn's char_wb) over lowercased text."""
    grams = set()
    for w in re.findall(r"\w+", text.lower(), re.U):
        w = " " + w + " "
        L = len(w)
        for n in range(nmin, nmax + 1):
            if L < n:
                break
            for i in range(L - n + 1):
                grams.add(w[i:i + n])
    return grams


CHAR_DIM = 1 << 21


def hash_gram(g: str) -> int:
    return zlib.crc32(g.encode("utf-8")) & (CHAR_DIM - 1)


def char_text(rec: dict) -> str:
    """Text fed to the char n-gram retriever: name subwords + doc head + statement head."""
    return " ".join([
        " ".join(split_ident(rec["name"])),
        (rec.get("doc") or "")[:300],
        (rec.get("statement") or "")[:200],
    ])


def dense_text(rec: dict) -> str:
    stmt = rec.get("statement") or ""
    stmt = "".join((" " + SYMBOL_WORDS[c] + " ") if c in SYMBOL_WORDS else c for c in stmt[:400])
    doc = _LATEX_CMD.sub(lambda m: " " + m.group(1) + " ", rec.get("doc") or "")
    return " ".join([humanize_name(rec["name"]), doc[:600], stmt])


def load_wordllama():
    """Load WordLlama from weights bundled inside the PyPI wheel (no network).

    Returns the model or None if wordllama is not importable."""
    try:
        import wordllama
        from wordllama import WordLlama
    except Exception:
        return None
    pkg = Path(wordllama.__file__).parent
    # wordllama 0.4.0 looks for <pkg>/tokenizer/... but ships <pkg>/tokenizers/...;
    # pointing cache_dir at the package dir makes its cache lookup find both files.
    return WordLlama.load(cache_dir=pkg, disable_download=True)


def rrf(rank_lists, k: int = 60, weights=None):
    """Reciprocal-rank fusion of several ranked lists of doc ids."""
    scores = {}
    for li, lst in enumerate(rank_lists):
        w = 1.0 if weights is None else weights[li]
        for r, d in enumerate(lst):
            scores[d] = scores.get(d, 0.0) + w / (k + r + 1)
    return sorted(scores, key=lambda d: -scores[d])
