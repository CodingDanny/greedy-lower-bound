# Lean formalisation of the Greedy lower bound

This project formalises the Ω(log n / log log n) lower bound on the
approximation ratio of global Greedy grammar compression. The bound holds
on an infinite family of inputs over growing alphabets, for every complete
execution with left-to-right occurrence replacement and arbitrary maximizing ties.

## Check the proof

Install [Lean through elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/CodingDanny/greedy-lower-bound.git
cd greedy-lower-bound/lean
lake exe cache get
lake build
lake env lean Audit.lean
```

The project uses Lean 4.19.0. `lean-toolchain` selects the compiler, and
`lake-manifest.json` pins Mathlib and its dependencies. Retain these files
when reproducing the proof. Downloading the Mathlib cache is optional;
without it, dependencies are built from source.

`lake build` checks the formalisation. `Audit.lean` additionally checks the
transitive axiom dependencies of all project theorems and requires the main
lower-bound statements to be present. It permits only `propext`,
`Classical.choice`, and `Quot.sound`, and rejects dependencies on admitted
proofs or additional axioms. Both commands must finish without errors.

## Main statements

All declarations below belong to the namespace `GreedyLowerBound`.

| Statement | Declaration | Source |
| --- | --- | --- |
| Input construction, optimum grammar size, and output bounds | `full_lower_bound` | [FinalTheorem.lean](lean/GreedyLowerBound/FinalTheorem.lean) |
| Logarithmic lower bound on arbitrarily large inputs | `greedy_logarithmic_lower_bound` | [FinalTheorem.lean](lean/GreedyLowerBound/FinalTheorem.lean) |
| No constant approximation ratio | `no_constant_approximation` | [FinalTheorem.lean](lean/GreedyLowerBound/FinalTheorem.lean) |
| Conclusions for the maximal-factor formulation of Greedy | `paper_greedy_logarithmic_lower_bound`, `paper_no_constant_approximation` | [PaperFinalTheorem.lean](lean/GreedyLowerBound/PaperFinalTheorem.lean) |

[PaperAlgorithm.lean](lean/GreedyLowerBound/PaperAlgorithm.lean) proves the
algorithm formulations equivalent. The construction and its analysis include
cyclic de Bruijn seeds, the power-free morphism, forced substitution phases,
factor counting, and a comparison grammar. Existence of complete executions
is also proved. [GreedyLowerBound.lean](lean/GreedyLowerBound.lean) imports
all mathematical modules.

## License

[Apache License 2.0](LICENSE).
