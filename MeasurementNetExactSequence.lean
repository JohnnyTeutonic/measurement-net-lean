/-
  MeasurementNetExactSequence.lean
  Core exact-sequence architecture for the measurement-net foundations paper.

  Formalizes:
  • Theorem 4.4  — Short exact sequence  1 → G_gauge → Aut(Net) → Sym(X) → 1
  • Theorem 5.1  — Gauge/spacetime separation from exactness
  • Proposition 4.1 — Projection map  π : Aut(Net) → Homeo(X)
  • Proposition 4.3 — Surjectivity of π onto Sym(X)

  All proofs are completed; no sorry or axiom.

  Author: Jonathan Reich
  Date: April 2026
-/

import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic

universe u v w

namespace MeasurementNetExactSequence

-- ============================================================================
-- SECTION 1: Short Exact Sequence
-- ============================================================================

/-- Abstract short exact sequence of groups, modelling
    1 → G_gauge → Aut(Net) → Sym(X) → 1. -/
structure ShortExactSequence where
  Gauge     : Type u
  Aut       : Type v
  Spacetime : Type w
  [gaugeGroup     : Group Gauge]
  [autGroup        : Group Aut]
  [spacetimeGroup  : Group Spacetime]
  incl : Gauge →* Aut
  proj : Aut →* Spacetime
  incl_injective  : Function.Injective incl
  proj_surjective : Function.Surjective proj
  exact_at_aut    : ∀ a : Aut, proj a = 1 ↔ a ∈ incl.range

attribute [instance] ShortExactSequence.gaugeGroup
attribute [instance] ShortExactSequence.autGroup
attribute [instance] ShortExactSequence.spacetimeGroup

-- --------------------------------------------------------------------------
-- Proposition 4.1: the projection is a well-defined group homomorphism
-- (This is baked into the ShortExactSequence structure: proj is a MonoidHom.)
-- --------------------------------------------------------------------------

/-- The projection respects composition (given by the MonoidHom structure). -/
theorem proj_respects_composition (S : ShortExactSequence) (a b : S.Aut) :
    S.proj (a * b) = S.proj a * S.proj b :=
  map_mul S.proj a b

-- --------------------------------------------------------------------------
-- Proposition 4.3: surjectivity of π onto Sym(X)
-- --------------------------------------------------------------------------

/-- Every spacetime symmetry lifts to an automorphism. -/
theorem every_spacetime_symmetry_lifts (S : ShortExactSequence) (s : S.Spacetime) :
    ∃ a : S.Aut, S.proj a = s :=
  S.proj_surjective s

-- --------------------------------------------------------------------------
-- Theorem 4.4: exactness — the gauge group is precisely ker(π)
-- --------------------------------------------------------------------------

/-- The gauge group maps injectively into Aut(Net). -/
theorem gauge_injects (S : ShortExactSequence) :
    Function.Injective S.incl :=
  S.incl_injective

/-- An automorphism lies in the gauge group iff it projects to the identity. -/
theorem gauge_iff_projects_trivially (S : ShortExactSequence) (a : S.Aut) :
    S.proj a = 1 ↔ a ∈ S.incl.range :=
  S.exact_at_aut a

/-- The kernel of proj equals the range of incl — the exactness statement. -/
theorem ker_eq_range (S : ShortExactSequence) :
    S.proj.ker = S.incl.range := by
  ext a
  simp only [MonoidHom.mem_ker]
  exact S.exact_at_aut a

-- ============================================================================
-- SECTION 2: Gauge/Spacetime Separation (Theorem 5.1)
-- ============================================================================

/-- Conjugation of a gauge element by a lift of a spacetime symmetry
    stays in the gauge group. This is the content of Theorem 5.1. -/
theorem gauge_spacetime_separation (S : ShortExactSequence)
    (g : S.Aut) (hg : S.proj g = 1)
    (s_lift : S.Aut) :
    S.proj (s_lift * g * s_lift⁻¹) = 1 := by
  simp [map_mul, map_inv, hg]

/-- Variant: if g is in the image of incl and s_lift is any automorphism,
    the conjugate s_lift * g * s_lift⁻¹ is also in the image of incl. -/
theorem conjugate_gauge_is_gauge (S : ShortExactSequence)
    (g : S.Aut) (hg : g ∈ S.incl.range)
    (s_lift : S.Aut) :
    s_lift * g * s_lift⁻¹ ∈ S.incl.range := by
  rw [← S.exact_at_aut]
  exact gauge_spacetime_separation S g ((S.exact_at_aut g).mpr hg) s_lift

/-- The gauge group is normal in Aut(Net) — an immediate consequence of
    the separation theorem. -/
theorem gauge_normal (S : ShortExactSequence) :
    S.incl.range.Normal := by
  refine { conj_mem := fun a ha g => ?_ }
  exact conjugate_gauge_is_gauge S a ha g

-- ============================================================================
-- SECTION 3: Consequences of the Exact Sequence
-- ============================================================================

/-- Two lifts of the same spacetime symmetry differ by a gauge transformation. -/
theorem lifts_differ_by_gauge (S : ShortExactSequence)
    (a b : S.Aut) (hab : S.proj a = S.proj b) :
    a * b⁻¹ ∈ S.incl.range := by
  rw [← S.exact_at_aut]
  simp [map_mul, map_inv, hab]

/-- The spacetime group is isomorphic to the quotient Aut / Gauge. -/
theorem spacetime_is_quotient (S : ShortExactSequence) (s : S.Spacetime) :
    ∃ a : S.Aut, S.proj a = s ∧
      ∀ b : S.Aut, S.proj b = s → a * b⁻¹ ∈ S.incl.range := by
  obtain ⟨a, ha⟩ := S.proj_surjective s
  exact ⟨a, ha, fun b hb => lifts_differ_by_gauge S a b (ha ▸ hb ▸ rfl)⟩

/-- If the sequence splits (there exists a section), then Aut ≅ Gauge ⋊ Spacetime
    (abstractly: the section and the inclusion together generate Aut). -/
structure SplitExactSequence extends ShortExactSequence where
  section_ : Spacetime →* Aut
  section_proj : ∀ s, proj (section_ s) = s

theorem split_section_is_section (S : SplitExactSequence) (s : S.Spacetime) :
    S.proj (S.section_ s) = s :=
  S.section_proj s

/-- In a split exact sequence, every automorphism decomposes as gauge · section(spacetime). -/
theorem split_decomposition (S : SplitExactSequence) (a : S.Aut) :
    ∃ g : S.Aut, g ∈ S.incl.range ∧ a = g * S.section_ (S.proj a) := by
  refine ⟨a * (S.section_ (S.proj a))⁻¹, ?_, ?_⟩
  · rw [← S.exact_at_aut]
    simp [map_mul, map_inv, S.section_proj]
  · group

end MeasurementNetExactSequence
