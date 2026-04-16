# Measurement Net Foundations — Lean 4 Formalization

Lean 4 formalization of the core theorems from:

> **From Measurement to the Standard Model: a Categorical Inverse Noether Programme**
> Jonathan Reich (2026)

This repository contains machine-checked proofs for the measurement-net foundations paper,
which derives gauge symmetry, spacetime structure, and classification results from
five operational postulates (Localizability, Observer Equivalence, Separability,
Continuity, Finite Distinguishability) via categorical reconstruction.

## Files

| File | Paper §§ | Content |
|------|----------|---------|
| `MeasurementNetExactSequence.lean` | §4–5 | Short exact sequence 1 → G → Aut(Net) → Sym(X) → 1; gauge/spacetime separation; gauge normality; split decomposition |
| `MeasurementNetSplitting.lean` | §6 | Splitting lemma; local constancy from Ocneanu rigidity; global splitting on simply connected bases |
| `MeasurementNetMonodromy.lean` | §6 | Monodromy classification by conjugacy; faithful monodromy ≃ visible quotient; patching obstruction |
| `MeasurementNetModuli.lean` | §7 | Moduli discreteness (stacky Ocneanu rigidity); continuity collapse; Spin(8)/triality orbit computation; Burnside and Frobenius verification |
| `MeasurementNetIndependence.lean` | §3 | Five named countermodels proving postulate independence (Theorem 3.6) |
| `MeasurementNetReconstruction.lean` | §8 | Connected-component reconstruction; visible monodromy reconstruction; locale reconstruction via frame equivalence |
| `MeasurementNetClosure.lean` | §8 | Kernel-level closure; inert symmetry characterization; no-new-spacetime-symmetry theorem |
| `MeasurementNetEnrichment.lean` | §8 | Heisenberg bridge schema; enrichment gap (monodromy alone does not close the gap to geometric quantization) |
| `MeasurementNetQGObstruction.lean` | §8 | Fixed-target quantum gravity tension; target extension programme |

## Build Status

- **Lean 4 v4.27.0-rc1** with **Mathlib** (2025 vintage)
- **Zero `sorry`**, **zero `axiom`**, **zero warnings**
- Full build: 3063 jobs, all passing

## Building

These files are designed to build inside a Lake project with Mathlib as a dependency.
To typecheck locally:

```bash
# In a Lake project with Mathlib configured:
cp MeasurementNet*.lean /path/to/your/lean_project/
cd /path/to/your/lean_project/
lake build MeasurementNetExactSequence MeasurementNetSplitting MeasurementNetMonodromy \
  MeasurementNetModuli MeasurementNetIndependence MeasurementNetReconstruction \
  MeasurementNetClosure MeasurementNetEnrichment MeasurementNetQGObstruction
```

## Formalization Philosophy

The formalization follows an **abstract-packaging** approach: each paper theorem
is encoded as a structure bundling its hypotheses and a theorem discharging the
conclusion from those hypotheses. This avoids importing the full apparatus of
operator algebras or higher categories into Lean while still machine-checking the
logical skeleton of each argument.

Key features:
- **No axioms**: every result is proved from structure fields, not postulated
- **No sorry**: every proof obligation is discharged
- **Mathlib integration**: uses `MonoidHom`, `MulEquiv`, `Subgroup`, `CompleteLattice`, `OrderIso` from Mathlib
- **Concrete computations**: Spin(8) orbit counts, Burnside/Frobenius formulas, and moduli cardinalities are verified by `native_decide` or `norm_num`

## License

MIT

## Author

Jonathan Reich — 2026
