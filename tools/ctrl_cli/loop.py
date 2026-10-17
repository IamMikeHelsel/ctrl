"""
ctrl loop: Fast local LLM-in-the-loop proof synthesis and auto-correction.
Driven by local Ollama coder models (e.g. qwen2.5-coder:7b) and verified
by instantaneous isolated Lean 4 scratchpad elaboration.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
from dataclasses import asdict, dataclass, field
from pathlib import Path

# ANSI Colors
BOLD = "\033[1m"
GREEN = "\033[32m"
BLUE = "\033[34m"
CYAN = "\033[36m"
YELLOW = "\033[33m"
RED = "\033[31m"
MAGENTA = "\033[35m"
DIM = "\033[2m"
RESET = "\033[0m"

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"

SYSTEM_PROMPT = """You are an expert Lean 4 formal proof engineer specializing in control theory, matrix algebra, and Mathlib.
Your task is to write clean, complete, and rigorous proofs in Lean 4 without any `sorry` or `admit`.

Domain context & available tools:
- The system automatically imports `ControlsLean` and `Mathlib`.
- ControlsLean quadratic form: `quad M x = x ⬝ᵥ (M *ᵥ x)`.
- Core matrix-vector identities:
  * `neg_mulVec M x : (-M) *ᵥ x = - (M *ᵥ x)`
  * `add_mulVec M N x : (M + N) *ᵥ x = M *ᵥ x + N *ᵥ x`
  * `sub_mulVec M N x : (M - N) *ᵥ x = M *ᵥ x - N *ᵥ x`
  * `smul_mulVec c M x : (c • M) *ᵥ x = c • (M *ᵥ x)`
  * `dotProduct_neg x v : x ⬝ᵥ (-v) = - (x ⬝ᵥ v)`
  * `dotProduct_add x u v : x ⬝ᵥ (u + v) = x ⬝ᵥ u + x ⬝ᵥ v`
  * `dotProduct_sub x u v : x ⬝ᵥ (u - v) = x ⬝ᵥ u - x ⬝ᵥ v`
  * `dotProduct_smul x c v : x ⬝ᵥ (c • v) = c * (x ⬝ᵥ v)`
  * `dotProduct_transpose_mulVec M x y : x ⬝ᵥ (Mᵀ *ᵥ y) = y ⬝ᵥ (M *ᵥ x)`
- Matrix multiplication & transposition:
  * `transpose_mul A B : (A * B)ᵀ = Bᵀ * Aᵀ`
  * `transpose_transpose A : (Aᵀ)ᵀ = A`
  * `Matrix.mul_assoc A B C : A * B * C = A * (B * C)`
- Nonnegativity:
  * `Finset.sum_nonneg : (∀ i ∈ s, 0 ≤ f i) → 0 ≤ ∑ i ∈ s, f i`
  * `mul_self_nonneg (a : ℝ) : 0 ≤ a * a`
- Common patterns in ControlsLean:
  * Additivity: `quad (M + N) x = quad M x + quad N x` is solved by `simp only [quad, add_mulVec, dotProduct_add]`
  * Negation: `quad (-M) x = - quad M x` is solved by `simp only [quad, neg_mulVec, dotProduct_neg]`
  * Transpose: `quad Mᵀ x = quad M x` is solved by `simp only [quad, dotProduct_transpose_mulVec]`
  * Transposition of products / Gramians: `(term A B i)ᵀ = term A B i` is solved by `unfold term; simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]`
  * Inner product nonnegativity: `0 ≤ v ⬝ᵥ v` is solved by `unfold dotProduct; apply Finset.sum_nonneg; intro j _; exact mul_self_nonneg (v j)`
  * General tactics: `simp`, `rw`, `unfold`, `ring`, `linarith`, `apply`, `exact`, `ext`, `intro`.

Output instructions:
- Output ONLY the complete theorem with its proof inside a ```lean ... ``` block.
- Do NOT output markdown explanations, commentary, or conversational preamble.
"""


@dataclass
class OllamaTiming:
    eval_count: int = 0
    eval_duration_sec: float = 0.0
    prompt_eval_count: int = 0
    prompt_eval_duration_sec: float = 0.0
    load_duration_sec: float = 0.0
    total_duration_sec: float = 0.0
    tok_per_sec: float = 0.0


@dataclass
class OllamaResponse:
    text: str
    timing: OllamaTiming
    error: str | None = None


class OllamaClient:
    """Client for querying the local Ollama API."""

    def __init__(
        self, base_url: str = "http://localhost:11434", model: str = "qwen2.5-coder:7b"
    ):
        self.base_url = base_url.rstrip("/")
        self.model = model

    def check_health(self) -> tuple[bool, str]:
        """Check if Ollama server is running and model is available."""
        url = f"{self.base_url}/api/tags"
        try:
            req = urllib.request.Request(url, method="GET")
            with urllib.request.urlopen(req, timeout=3.0) as resp:
                data = json.loads(resp.read().decode())
                models = [m.get("name") for m in data.get("models", [])]
                # Match model name with or without tag
                match = any(
                    self.model == m or m.startswith(f"{self.model}:") for m in models
                )
                if not match:
                    available = ", ".join(models) if models else "none"
                    return (
                        False,
                        f"Model '{self.model}' not found in Ollama. Available: {available}",
                    )
                return True, "Ollama is ready"
        except urllib.error.URLError as e:
            return False, f"Cannot connect to Ollama at {self.base_url}: {e}"
        except Exception as e:
            return False, f"Ollama health check failed: {e}"

    def generate(
        self,
        prompt: str,
        system: str = SYSTEM_PROMPT,
        temperature: float = 0.1,
        num_predict: int = 512,
        timeout: float = 60.0,
    ) -> OllamaResponse:
        """Query Ollama generate endpoint."""
        url = f"{self.base_url}/api/generate"
        payload = {
            "model": self.model,
            "system": system,
            "prompt": prompt,
            "stream": False,
            "options": {
                "temperature": temperature,
                "num_predict": num_predict,
            },
        }

        data_bytes = json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            url,
            data=data_bytes,
            headers={"Content-Type": "application/json"},
            method="POST",
        )

        t_start = time.time()
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                res = json.loads(resp.read().decode())
                eval_count = res.get("eval_count", 0)
                eval_dur = res.get("eval_duration", 0) / 1e9
                prompt_eval_count = res.get("prompt_eval_count", 0)
                prompt_eval_dur = res.get("prompt_eval_duration", 0) / 1e9
                load_dur = res.get("load_duration", 0) / 1e9
                total_dur = res.get("total_duration", 0) / 1e9 or (
                    time.time() - t_start
                )
                tok_per_sec = (eval_count / eval_dur) if eval_dur > 0 else 0.0

                timing = OllamaTiming(
                    eval_count=eval_count,
                    eval_duration_sec=eval_dur,
                    prompt_eval_count=prompt_eval_count,
                    prompt_eval_duration_sec=prompt_eval_dur,
                    load_duration_sec=load_dur,
                    total_duration_sec=total_dur,
                    tok_per_sec=tok_per_sec,
                )
                return OllamaResponse(
                    text=res.get("response", ""),
                    timing=timing,
                )
        except urllib.error.URLError as e:
            return OllamaResponse(
                text="",
                timing=OllamaTiming(total_duration_sec=time.time() - t_start),
                error=f"Connection to Ollama failed: {e}",
            )
        except Exception as e:
            return OllamaResponse(
                text="",
                timing=OllamaTiming(total_duration_sec=time.time() - t_start),
                error=f"Ollama generation error: {e}",
            )


@dataclass
class VerificationResult:
    success: bool
    duration_sec: float
    exit_code: int
    stdout: str
    stderr: str
    diagnostic: str = ""


class LeanVerifier:
    """Verifies candidate Lean snippets using ./ctrl scratch."""

    def __init__(self, imports: str = "ControlsLean"):
        self.imports = imports

    def verify(self, code: str, timeout: float = 60.0) -> VerificationResult:
        """Run scratch_check.sh in strict mode."""
        cmd = [
            str(SCRIPTS_DIR / "scratch_check.sh"),
            "-s",
            "-i",
            self.imports,
            "-c",
            code,
        ]

        t0 = time.time()
        try:
            proc = subprocess.run(
                cmd,
                cwd=str(REPO_ROOT),
                capture_output=True,
                text=True,
                timeout=timeout,
            )
            duration = time.time() - t0
            success = proc.returncode == 0
            diagnostic = (
                self._extract_diagnostic(proc.stdout, proc.stderr)
                if not success
                else ""
            )
            return VerificationResult(
                success=success,
                duration_sec=duration,
                exit_code=proc.returncode,
                stdout=proc.stdout,
                stderr=proc.stderr,
                diagnostic=diagnostic,
            )
        except subprocess.TimeoutExpired:
            return VerificationResult(
                success=False,
                duration_sec=time.time() - t0,
                exit_code=-1,
                stdout="",
                stderr="Elaboration timed out",
                diagnostic=f"Elaboration timed out after {timeout:.1f}s",
            )
        except Exception as e:
            return VerificationResult(
                success=False,
                duration_sec=time.time() - t0,
                exit_code=-1,
                stdout="",
                stderr=str(e),
                diagnostic=f"Verification script error: {e}",
            )

    def _extract_diagnostic(self, stdout: str, stderr: str) -> str:
        """Extract a clean, concise diagnostic from Lean compiler output."""
        lines = []
        # Filter stdout for errors and goals
        capture = False
        for line in stdout.splitlines():
            # Error header
            if ": error:" in line:
                # Strip absolute/temp path prefix
                parts = line.split(": error:", 1)
                clean_loc = parts[0].split("/")[-1]
                lines.append(f"{clean_loc}: error:{parts[1]}")
                capture = True
            elif capture:
                # Continue capturing indented context or goal
                if (
                    line.startswith("  ")
                    or line.startswith("⊢")
                    or line.startswith("case ")
                    or line.startswith("state:")
                ):
                    lines.append(line)
                elif line.strip() == "":
                    continue
                else:
                    capture = False

        if not lines:
            # Fallback to stderr or first few lines of stdout
            err_lines = [
                line
                for line in (stderr + "\n" + stdout).splitlines()
                if "FAILED" in line or "error" in line
            ]
            return (
                "\n".join(err_lines[:5])
                if err_lines
                else "Unknown Lean elaboration failure."
            )

        return "\n".join(lines[:10])


class CandidateExtractor:
    """Extracts Lean code from model output."""

    @staticmethod
    def extract(text: str, original_template: str) -> str:
        """Extract valid Lean 4 code from model response."""
        # 1. Search for ```lean ... ``` fence
        pattern = r"```(?:lean|lean4)?\s*(.*?)\s*```"
        matches = re.findall(pattern, text, re.DOTALL)
        if matches and matches[0].strip():
            code = matches[0].strip()
        else:
            # Strip partial or unclosed markdown fences
            cleaned = re.sub(r"^```(?:lean|lean4)?\s*", "", text.strip())
            cleaned = re.sub(r"\s*```$", "", cleaned)
            code = cleaned.strip()

        # 2. Check if the model only gave the tactic body (e.g. starts with 'by' or list of tactics)
        if not re.search(r"\b(theorem|lemma)\b", code):
            # The model returned only the proof block
            tactic_body = code
            if not tactic_body.startswith("by"):
                tactic_body = f"by\n  {tactic_body}"
            # Replace 'by sorry' or 'by\n  sorry' in template
            if "by sorry" in original_template:
                code = original_template.replace("by sorry", tactic_body)
            elif "by\n  sorry" in original_template:
                code = original_template.replace("by\n  sorry", tactic_body)
            elif ":=" in original_template:
                # Replace everything after ':='
                prefix = original_template.split(":=")[0].rstrip()
                code = f"{prefix} :=\n{tactic_body}"

        return code


@dataclass
class IterationRecord:
    iteration: int
    prompt_tokens: int
    eval_tokens: int
    tok_per_sec: float
    gen_time_sec: float
    elab_time_sec: float
    total_time_sec: float
    success: bool
    code: str
    diagnostic: str = ""


@dataclass
class LoopResult:
    goal_name: str
    success: bool
    iterations_run: int
    total_tokens: int
    avg_tok_per_sec: float
    total_loop_time_sec: float
    iterations: list[IterationRecord] = field(default_factory=list)
    final_code: str = ""


class ProofLoop:
    """Manages the generate -> elaborate -> auto-correct loop."""

    def __init__(
        self,
        client: OllamaClient,
        verifier: LeanVerifier,
        max_tries: int = 3,
        temperature: float = 0.1,
        timeout: float = 60.0,
        verbose: bool = False,
    ):
        self.client = client
        self.verifier = verifier
        self.max_tries = max_tries
        self.temperature = temperature
        self.timeout = timeout
        self.verbose = verbose

    def solve(self, theorem_code: str, goal_name: str = "goal") -> LoopResult:
        """Execute the self-correction loop on a single theorem."""
        iterations: list[IterationRecord] = []
        current_prompt = self._build_initial_prompt(theorem_code)
        candidate_code = ""

        t_loop_start = time.time()
        success = False

        for turn in range(1, self.max_tries + 1):
            if self.verbose:
                print(
                    f"{DIM}[Turn {turn}/{self.max_tries}] Querying {self.client.model}...{RESET}"
                )

            # 1. Model generation
            t_gen_start = time.time()
            resp = self.client.generate(
                prompt=current_prompt,
                temperature=self.temperature,
            )
            t_gen = time.time() - t_gen_start

            if resp.error:
                print(f"{RED}✗ Ollama error: {resp.error}{RESET}")
                iterations.append(
                    IterationRecord(
                        iteration=turn,
                        prompt_tokens=0,
                        eval_tokens=0,
                        tok_per_sec=0.0,
                        gen_time_sec=t_gen,
                        elab_time_sec=0.0,
                        total_time_sec=t_gen,
                        success=False,
                        code="",
                        diagnostic=resp.error,
                    )
                )
                break

            candidate_code = CandidateExtractor.extract(resp.text, theorem_code)

            # 2. Lean elaboration
            if self.verbose:
                print(
                    f"{DIM}[Turn {turn}/{self.max_tries}] Elaborating candidate in scratchpad...{RESET}"
                )

            ver_res = self.verifier.verify(candidate_code, timeout=self.timeout)
            total_turn_time = t_gen + ver_res.duration_sec

            record = IterationRecord(
                iteration=turn,
                prompt_tokens=resp.timing.prompt_eval_count,
                eval_tokens=resp.timing.eval_count,
                tok_per_sec=resp.timing.tok_per_sec,
                gen_time_sec=resp.timing.eval_duration_sec or t_gen,
                elab_time_sec=ver_res.duration_sec,
                total_time_sec=total_turn_time,
                success=ver_res.success,
                code=candidate_code,
                diagnostic=ver_res.diagnostic,
            )
            iterations.append(record)

            if ver_res.success:
                success = True
                if self.verbose:
                    print(
                        f"{GREEN}✓ Turn {turn}: Elaboration SUCCEEDED ({ver_res.duration_sec:.2f}s)!{RESET}"
                    )
                break
            else:
                if self.verbose:
                    print(
                        f"{YELLOW}⚠ Turn {turn}: Elaboration failed ({ver_res.duration_sec:.2f}s). Diagnostic:{RESET}\n"
                        f"{DIM}{ver_res.diagnostic}{RESET}"
                    )
                # Formulate auto-correction prompt
                current_prompt = self._build_correction_prompt(
                    candidate=candidate_code,
                    diagnostic=ver_res.diagnostic,
                )

        t_total = time.time() - t_loop_start
        total_tokens = sum(it.eval_tokens for it in iterations)
        tok_speeds = [it.tok_per_sec for it in iterations if it.tok_per_sec > 0]
        avg_tok_per_sec = (sum(tok_speeds) / len(tok_speeds)) if tok_speeds else 0.0

        return LoopResult(
            goal_name=goal_name,
            success=success,
            iterations_run=len(iterations),
            total_tokens=total_tokens,
            avg_tok_per_sec=avg_tok_per_sec,
            total_loop_time_sec=t_total,
            iterations=iterations,
            final_code=candidate_code,
        )

    def _build_initial_prompt(self, theorem_code: str) -> str:
        return f"""Here is the Lean 4 theorem to prove:
```lean
{theorem_code}
```

Write the complete theorem with the proof replacing `sorry`.
Output ONLY the code inside a ```lean ... ``` block."""

    def _build_correction_prompt(self, candidate: str, diagnostic: str) -> str:
        hints = []
        if "No goals to be solved" in diagnostic:
            hints.append(
                "The proof completed earlier than expected. Remove unnecessary trailing tactics."
            )
        elif "Did not find an occurrence of the pattern" in diagnostic:
            if "?a * -?b" in diagnostic or "-?b" in diagnostic:
                hints.append(
                    "Do not use scalar `mul_neg` for matrix negation. Use `neg_mulVec` and `dotProduct_neg`, or `simp [quad, neg_mulVec, dotProduct_neg]`."
                )
            elif "?u ⬝ᵥ (?v + ?w)" in diagnostic or "+?w" in diagnostic:
                hints.append(
                    "Rewrite pattern not found. Apply `add_mulVec` before `dotProduct_add`, or use `simp [quad, add_mulVec, dotProduct_add]`."
                )
            else:
                hints.append(
                    "Rewrite pattern not found. Check if an intermediate simplification (e.g. `add_mulVec`, `sub_mulVec`, `neg_mulVec`) must be applied first, or try `simp [...]`."
                )
        elif "Type mismatch" in diagnostic:
            hints.append(
                "Type mismatch. Verify lemma argument types, order, and namespace."
            )
        elif "unknown identifier" in diagnostic:
            hints.append(
                "Unknown identifier. Ensure identifiers match standard Mathlib or ControlsLean names."
            )
        elif "unsolved goals" in diagnostic:
            hints.append(
                "Unsolved goals remain. Provide additional steps or check remaining goal state."
            )
        elif "timed out" in diagnostic:
            hints.append(
                "Elaboration timed out. Avoid slow search tactics; use explicit lemmas with `simp only [...]` or `rw [...]`."
            )
        elif (
            "expected '_' or identifier" in diagnostic
            or "unexpected token '('" in diagnostic
        ):
            hints.append(
                "Lean 4 syntax error: `case` statements do not use parentheses. Use `case inl j =>` instead of `case (inl j)`."
            )

        hint_text = "\n".join(f"- Hint: {h}" for h in hints)
        if hint_text:
            hint_text = f"\nSpecific Guidance:\n{hint_text}\n"

        return f"""The previous candidate failed Lean elaboration.

Failed Candidate:
```lean
{candidate}
```

Compiler Error Diagnostic:
{diagnostic}
{hint_text}
Fix the error and output the complete corrected Lean code inside a ```lean ... ``` block:"""


# Canonical benchmark lemmas from ControlsLean
BENCHMARK_LEMMAS = [
    {
        "name": "quad_add",
        "description": "Quadratic form additivity over matrices",
        "code": """open Matrix ControlsLean.Controls

theorem quad_add {n : Type*} [Fintype n] (M N : Matrix n n ℝ) (x : n → ℝ) :
    quad (M + N) x = quad M x + quad N x := by
  sorry""",
    },
    {
        "name": "quad_neg",
        "description": "Quadratic form negation over matrices",
        "code": """open Matrix ControlsLean.Controls

theorem quad_neg {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    quad (-M) x = - quad M x := by
  sorry""",
    },
    {
        "name": "quad_transpose",
        "description": "Invariance of quadratic form under transpose",
        "code": """open Matrix ControlsLean.Controls

theorem quad_transpose {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    quad Mᵀ x = quad M x := by
  sorry""",
    },
    {
        "name": "term_transpose",
        "description": "Symmetry of Gramian stage summand",
        "code": """open Matrix ControlsLean.Controls

variable {n m : ℕ}

theorem term_transpose (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (i : ℕ) :
    (term A B i)ᵀ = term A B i := by
  sorry""",
    },
    {
        "name": "dotProduct_self_nonneg",
        "description": "Nonnegativity of vector inner product with itself",
        "code": """open Matrix BigOperators

variable {m : ℕ}

theorem dotProduct_self_nonneg (v : Fin m → ℝ) : 0 ≤ v ⬝ᵥ v := by
  sorry""",
    },
]


def run_benchmark(
    client: OllamaClient,
    verifier: LeanVerifier,
    max_tries: int = 3,
    temperature: float = 0.1,
    timeout: float = 60.0,
    verbose: bool = False,
) -> list[LoopResult]:
    """Execute the full benchmark suite across canonical lemmas."""
    print(f"\n{BOLD}{CYAN}=== Starting Lean 4 Proof Loop Benchmark ==={RESET}")
    print(
        f"Model: {GREEN}{client.model}{RESET} | Max Tries: {YELLOW}{max_tries}{RESET} | Temp: {CYAN}{temperature}{RESET} | Timeout: {CYAN}{timeout:.0f}s{RESET}\n"
    )

    loop = ProofLoop(
        client=client,
        verifier=verifier,
        max_tries=max_tries,
        temperature=temperature,
        timeout=timeout,
        verbose=verbose,
    )

    results: list[LoopResult] = []

    for idx, item in enumerate(BENCHMARK_LEMMAS, 1):
        name = item["name"]
        desc = item["description"]
        code = item["code"]

        print(
            f"{BOLD}[{idx}/{len(BENCHMARK_LEMMAS)}] Benchmarking: {CYAN}{name}{RESET} ({desc})..."
        )
        t0 = time.time()
        res = loop.solve(theorem_code=code, goal_name=name)
        elapsed = time.time() - t0

        status_str = f"{GREEN}SOLVED{RESET}" if res.success else f"{RED}FAILED{RESET}"
        tries_str = f"{res.iterations_run} turn(s)"
        print(
            f"  Result: {status_str} in {tries_str} | Total Time: {elapsed:.2f}s | "
            f"Tokens: {res.total_tokens} @ {res.avg_tok_per_sec:.1f} tok/s"
        )
        for it in res.iterations:
            sub_status = f"{GREEN}✓{RESET}" if it.success else f"{RED}✗{RESET}"
            print(
                f"    {sub_status} Turn {it.iteration}: LLM: {it.gen_time_sec:.2f}s ({it.eval_tokens} tok @ {it.tok_per_sec:.1f} tok/s) "
                f"+ Lean: {it.elab_time_sec:.2f}s = {it.total_time_sec:.2f}s"
            )
            if not it.success and it.diagnostic:
                first_line = it.diagnostic.strip().splitlines()[0]
                print(f"      {DIM}Error: {first_line}{RESET}")
        print()
        results.append(res)

    print_summary_table(results)
    return results


def print_summary_table(results: list[LoopResult]):
    """Print an aggregate summary table of benchmark results."""
    print(f"{BOLD}{CYAN}=== Benchmark Results Summary ==={RESET}\n")
    header = f"{'Lemma':<25} | {'Status':<10} | {'Turns':<6} | {'Tokens':<7} | {'tok/s':<8} | {'LLM Time':<9} | {'Lean Time':<10} | {'Total Time':<10}"
    print(BOLD + header + RESET)
    print("-" * len(header))

    total_tokens = 0
    total_llm_time = 0.0
    total_lean_time = 0.0
    total_wall_time = 0.0
    solved_count = 0

    for r in results:
        status = "SOLVED" if r.success else "FAILED"
        status_color = GREEN if r.success else RED
        total_tokens += r.total_tokens
        llm_t = sum(it.gen_time_sec for it in r.iterations)
        lean_t = sum(it.elab_time_sec for it in r.iterations)
        total_llm_time += llm_t
        total_lean_time += lean_t
        total_wall_time += r.total_loop_time_sec
        if r.success:
            solved_count += 1

        print(
            f"{r.goal_name:<25} | {status_color}{status:<10}{RESET} | {r.iterations_run:<6} | "
            f"{r.total_tokens:<7} | {r.avg_tok_per_sec:<8.1f} | {llm_t:<9.2f} | {lean_t:<10.2f} | {r.total_loop_time_sec:<10.2f}"
        )

    print("-" * len(header))
    avg_speed = (total_tokens / total_llm_time) if total_llm_time > 0 else 0.0
    success_rate = (solved_count / len(results)) * 100 if results else 0.0
    print(
        f"{'TOTAL / AGGREGATE':<25} | {solved_count}/{len(results)} ({success_rate:.0f}%) | "
        f"{'-':<6} | {total_tokens:<7} | {avg_speed:<8.1f} | {total_llm_time:<9.2f} | {total_lean_time:<10.2f} | {total_wall_time:<10.2f}\n"
    )


def run_loop_cli(args):
    """CLI handler for `ctrl loop`."""
    client = OllamaClient(base_url=args.url, model=args.model)

    # Health check
    ready, msg = client.check_health()
    if not ready:
        print(f"{RED}Error: {msg}{RESET}")
        print(
            f"{YELLOW}Ensure Ollama is running (`ollama serve`) and model `{args.model}` is pulled.{RESET}"
        )
        sys.exit(1)

    verifier = LeanVerifier(imports=args.imports)

    timeout = getattr(args, "timeout", 60.0)

    if args.benchmark:
        results = run_benchmark(
            client=client,
            verifier=verifier,
            max_tries=args.max_tries,
            temperature=args.temperature,
            timeout=timeout,
            verbose=args.verbose,
        )
        if args.json:
            out_data = [asdict(r) for r in results]
            print(json.dumps(out_data, indent=2))
        sys.exit(0 if all(r.success for r in results) else 1)

    # Single theorem mode
    goal_code = ""
    goal_name = "custom_goal"

    if args.file:
        file_path = Path(args.file)
        if not file_path.exists():
            print(f"{RED}Error: File not found: {file_path}{RESET}")
            sys.exit(1)
        goal_code = file_path.read_text(encoding="utf-8")
        goal_name = file_path.stem
    elif args.goal:
        # Check if argument is a file
        candidate_file = Path(args.goal)
        if candidate_file.exists() and candidate_file.is_file():
            goal_code = candidate_file.read_text(encoding="utf-8")
            goal_name = candidate_file.stem
        else:
            goal_code = args.goal
    else:
        print(
            f"{RED}Error: No theorem statement or benchmark requested. Use --help or --benchmark.{RESET}"
        )
        sys.exit(1)

    loop = ProofLoop(
        client=client,
        verifier=verifier,
        max_tries=args.max_tries,
        temperature=args.temperature,
        timeout=timeout,
        verbose=args.verbose,
    )

    print(f"\n{BOLD}{CYAN}=== Starting Proof Loop for: {goal_name} ==={RESET}")
    print(
        f"Model: {GREEN}{client.model}{RESET} | Max Tries: {YELLOW}{args.max_tries}{RESET}\n"
    )

    res = loop.solve(theorem_code=goal_code, goal_name=goal_name)

    if res.success:
        print(f"\n{BOLD}{GREEN}✓ Theorem Solved Successfully!{RESET}")
        print(f"{BOLD}Final Verified Lean Code:{RESET}\n")
        print(f"```lean\n{res.final_code}\n```")
    else:
        print(
            f"\n{BOLD}{RED}✗ Failed to prove theorem within {args.max_tries} tries.{RESET}"
        )
        if res.iterations:
            print(
                f"{BOLD}Last Diagnostic:{RESET}\n{DIM}{res.iterations[-1].diagnostic}{RESET}"
            )

    if args.json:
        print(json.dumps(asdict(res), indent=2))

    sys.exit(0 if res.success else 1)
