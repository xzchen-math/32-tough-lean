# 32-tough-lean

A Lean formalization project for the manuscript `v4.tex` on Hamiltonicity of 3/2-tough, 2K₂-free graphs.

**Current status: partial formalization. The existing modules pass Lean compilation and the axiom dependency audit, but the manuscript's main theorem has not yet been proved unconditionally in Lean.**

The original manuscript is `../3:2-tough-2K_2-free/论文/v4.tex`. An unchanged snapshot is included as `source/v4.tex`, with its SHA-256 recorded in `source/metadata.json`. The original file has not been modified.

## Verified results

- Definitions of graphs, independent sets, maximum independent sets, neighborhoods, connected components after vertex deletion, 3/2-toughness, simple paths, simple cycles, and Hamiltonicity. For graphs with at least three vertices, the Hamiltonicity definition is proved equivalent to mathlib's definition.
- The three structural properties in Fact 2.1: comparability of neighborhoods of vertices in an independent set, realization of their neighborhood union by a single vertex, and the existence of at most one component containing an edge after vertex deletion.
- Claim 2.1: a longest admissible path is dominating, including an explicit path-extension construction.
- Counting arguments for threshold deletion, exchanges, and two-for-one exchanges, together with termination of bounded strictly increasing sequences.
- Two finite maximization steps and the maximum-independent-set exchange argument under the required predecessor-set properties.
- The neighborhood-union identity in Section 4, two upper bounds on set sizes, a lower bound on the actual number of connected components contributed by isolated vertices, and the final toughness contradiction.
- The final deduction from a given `FinalConfiguration`. **Constructing this configuration remains an open proof obligation.**
- The explicit graphs in Chvátal's example, their split and 2K₂-free properties, vertex counts, and convergence to the threshold. Their toughness and non-Hamiltonicity are taken from the literature as black-box results; these are then used to prove sharpness for every real number `t < 3/2`.

See [STATUS.md](STATUS.md) for the detailed correspondence with the manuscript. The number of auxiliary theorems should not be interpreted as the fraction of the manuscript that has been formalized.

## Remaining proof obligations

The predecessor-structure lemmas, path and cycle order bounds, restricted-cycle-family corollary, almost-spanning cycle, two omitted-vertex lemmas, major parts of the structural lemma, and constructions of the rotation endpoint sets and the three counting claims have not all been formalized.

`Broersma/Manuscript.lean` records translated but unproved propositions as `def ...Statement : Prop`. These definitions do not assert that the propositions are true. The stage-closure condition in the restricted-cycle-family corollary and the full rotation process have not yet been transcribed in full.

The theorem in `Broersma/MainReduction.lean`,

```lean
theorem main_of_configuration (G : SimpleGraph V)
    (construct : InternalConstruction G) : MainTheoremStatement G
```

explicitly requires the unproved internal hypothesis `construct`. There is currently no unconditional `Broersma.main`. `FinalConfiguration` is a record of data and properties sufficient to derive a contradiction; its three claim fields are assumptions, not proofs obtained merely by declaring the structure.

## External black-box results

The four custom axioms are collected in `Broersma/External.lean`, each with a source:

1. Kratsch–Lehel–Müller: Hamiltonicity of 3/2-tough split graphs.
2. Ota–Sanka, Proposition 1.6: existence of a 2-factor.
3. Ota–Sanka, Lemma 3.3 and the almost-spanning-cycle special case of its proof: independence of the successor set and a degree bound.
4. The exact toughness, non-Hamiltonicity, and absence of a 2-factor for Chvátal's published split-graph examples, used only for sharpness.

No unproved internal lemma from this manuscript is declared as an axiom. The project does not use `sorry`, `admit`, or `native_decide`. Proofs may use the standard Lean/mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`. `Audit.lean` automatically rejects any additional axiom dependencies.

## Running verification

Lean and mathlib are pinned to `v4.33.0-rc2`, with mathlib at commit `51e6992efd06126df61a496bebf8f49482a4e129`. Lake dependency revisions are recorded in `lake-manifest.json`. The local project has a copied dependency cache and does not rely on absolute import paths into another project.

From the local project directory or the root of a cloned repository, run:

```sh
lake build
python3 verify.py
```

The default verification command checks the completed modules and also reports the outcome of the main-theorem check. **Exit code 0 means only that the partial proof library and the axiom audit passed.**

```sh
python3 verify.py --require-complete
```

This command additionally requires the main theorem to follow from only the manuscript's three hypotheses. The current expected exit code is **2**, because the main theorem has not yet been proved. The conditional version with the additional `InternalConstruction` hypothesis does not satisfy this check.

Verification logs are stored in `verification/`: `build.log`, `axioms.log`, `complete-main.log`, and `report.json`.

On a fresh machine without a dependency cache, first install the specified Lean version, then run `lake update` and `lake exe cache get`. These commands require network access.

## Next steps

First complete the predecessor-structure results and cycle/path bounds in `Manuscript.lean`, and implement the actual rotation construction. Ultimately, prove `InternalConstruction G` and use `main_of_configuration` to define an unconditional `Broersma.main`. Then run strict verification and check that `#print axioms Broersma.main` lists only the permitted external axioms and Lean's foundational axioms described above.
