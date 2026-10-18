# Log: Erdős 261 (part i)

- 2026-10-17 · Antigravity Subagent 5. Selected `Erdos261.erdos_261.parts.i` (`{n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite`) from Formal Conjectures (`d9ce556`).
- Formalized the Borwein–Loring telescoping sum construction in `erdos/ErdosLab/Erdos261.lean`, proving:
  - `borwein_loring`: exact proof of `Erdos261.erdos_261.variants.borwein_loring`
  - `borwein_loring_property`: exact proof of `Erdos261.erdos_261.variants.borwein_loring_property`
  - `solution : statement`: exact proof of `Erdos261.erdos_261.parts.i` via `Set.infinite_of_injective_forall_mem` on `blSeq k = 2 ^ (k + 3) - (k + 2) - 2`.
- Approved statement (`ctrl approve 261 --by mike`, sha256 `dcf86bf48539f22a5532a4db0f88d4f83fabe14d14b3921b2cce81196db1a9f7`).
- `uv run ctrl check 261`: build, tokens, axioms (`propext`, `Classical.choice`, `Quot.sound`), binding, and hash all `ok`.
