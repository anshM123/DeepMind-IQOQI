# Machine-checked solutions of open problems from Formal Conjectures and the IQOQI Open Quantum Problems

**Authors:** Ansh Mishra, Aryan Senthilkumar. **License:** MIT.

Each folder settles open statements from Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) repository or from the IQOQI Vienna
[Open Quantum Problems](https://oqp.iqoqi.oeaw.ac.at/open-quantum-problems) list.

Every folder contains:
- a Lean 4 proof of the repository's exact statement, checked against the unmodified statement file with only the standard axioms;
- an independent check;
- verification logs;
- the record of the prior-work search.

| Folder | Problem | Result |
|---|---|---|
| [`OEIS-A051903/`](OEIS-A051903/) | `OeisA51903.conjecture2`, `conjecture3` (T. Ordowski, 2019) | `conjecture2`: **False**; `conjecture3`: **True**, witness `n = 7·631·881·3511²·201961` |

Related repositories by the same authors:
- IQOQI problems: [IQOQI-Conjecture](https://github.com/anshM123/IQOQI-Conjecture) (symmetrically thermalizing unitaries, every d);
- [GYNI-Causal-Problem](https://github.com/anshM123/GYNI-Causal-Problem);
- [Tavakoli-Morelli-Conjecture](https://github.com/anshM123/Tavakoli-Morelli-Conjecture);
- [CGLMP](https://github.com/anshM123/CGLMP) (OQP 27B, d = 3..12).
