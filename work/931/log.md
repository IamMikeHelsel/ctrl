# Log: Erdős 931 (`additional_condition_nonempty`)

- 2026-10-17 · Antigravity Subagent 5. Selected `Erdos931.erdos_931.variants.additional_condition_nonempty` from Formal Conjectures (`d9ce556`).
- Ran a Python search for positive-integer symmetric $k_1 = k_2 = 3$ counterexamples to $n_2 > 2(n_1 + k_1)$ and discovered $(n_1, n_2) \in \{(2, 7), (3, 7), (4, 13), (11, 25), (33, 48), (53, 97), (54, 74), (168, 322)\}$.
- Formalized `counterexample_3_3_2_7`, `counterexample_3_3_3_7_no_strict_between_prime`, and `solution : statement` in `erdos/ErdosLab/Erdos931.lean`, all checked by `decide +kernel`.
- Approved statement (`erdos approve 931 --by mike`, sha256 `2e1339f075c41dc5c5464748310dd2528504e07d6085952610bbc538322ffa05`).
- `uv run erdos check 931`: build, tokens, axioms (`propext`, `Classical.choice`, `Quot.sound`), binding, and hash all `ok`.
