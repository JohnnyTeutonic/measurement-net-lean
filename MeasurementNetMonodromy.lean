import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

universe u v w

namespace MeasurementNetMonodromy

def ConjugateRepresentations {G : Type u} {H : Type v} [Group G] [Group H]
    (ρ σ : G →* H) : Prop :=
  ∃ h : H, ∀ g : G, σ g = h * ρ g * h⁻¹

theorem conjugateRepresentations_refl {G : Type u} {H : Type v} [Group G] [Group H]
    (ρ : G →* H) : ConjugateRepresentations ρ ρ := by
  refine ⟨1, ?_⟩
  intro g
  simp

structure MonodromyClassification where
  Loop : Type u
  loopGroup : Group Loop
  FiberAut : Type v
  fiberAutGroup : Group FiberAut
  Sector : Type w
  monodromyOf : Sector → Loop →* FiberAut
  sameGlobalSector : Sector → Sector → Prop
  classified_by_conjugacy :
    ∀ S T : Sector, sameGlobalSector S T ↔ ConjugateRepresentations (monodromyOf S) (monodromyOf T)

attribute [instance] MonodromyClassification.loopGroup
attribute [instance] MonodromyClassification.fiberAutGroup

 theorem operational_sector_equivalence_criterion (M : MonodromyClassification) (S T : M.Sector) :
    M.sameGlobalSector S T ↔ ConjugateRepresentations (M.monodromyOf S) (M.monodromyOf T) := by
  exact M.classified_by_conjugacy S T

 def visibleQuotient {G : Type u} {H : Type v} [Group G] [Group H] (ρ : G →* H) : Subgroup H :=
  ρ.range

 theorem operationally_visible_quotient_is_range {G : Type u} {H : Type v} [Group G] [Group H]
    (ρ : G →* H) : visibleQuotient ρ = ρ.range := rfl

 noncomputable def faithfulMonodromyEquivVisibleQuotient {G : Type u} {H : Type v}
    [Group G] [Group H] (ρ : G →* H) (hρ : Function.Injective ρ) :
    G ≃* visibleQuotient ρ := by
  let ρ' : G →* visibleQuotient ρ := ρ.rangeRestrict
  have hbij : Function.Bijective ρ' := by
    constructor
    · intro a b hab
      apply hρ
      exact congrArg Subtype.val hab
    · intro y
      rcases y with ⟨y, hy⟩
      rcases hy with ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      rfl
  exact MulEquiv.ofBijective ρ' hbij

 theorem faithful_monodromy_recovers_visible_quotient {G : Type u} {H : Type v}
    [Group G] [Group H] (ρ : G →* H) (hρ : Function.Injective ρ) :
    Nonempty (G ≃* visibleQuotient ρ) := by
  exact ⟨faithfulMonodromyEquivVisibleQuotient ρ hρ⟩

structure PatchingObstruction where
  Loop : Type u
  loopGroup : Group Loop
  FiberAut : Type v
  fiberAutGroup : Group FiberAut
  monodromy : Loop →* FiberAut
  globallyTrivializable : Prop
  global_trivialization_forces_trivial_monodromy :
    globallyTrivializable → ∀ g : Loop, monodromy g = 1

attribute [instance] PatchingObstruction.loopGroup
attribute [instance] PatchingObstruction.fiberAutGroup

 theorem global_trivialization_forces_trivial_monodromy (P : PatchingObstruction) :
    P.globallyTrivializable → ∀ g : P.Loop, P.monodromy g = 1 := by
  exact P.global_trivialization_forces_trivial_monodromy

 theorem nontrivial_monodromy_prevents_global_trivialization (P : PatchingObstruction) :
    (∃ g : P.Loop, P.monodromy g ≠ 1) → ¬ P.globallyTrivializable := by
  intro hnon hglob
  rcases hnon with ⟨g, hg⟩
  exact hg (P.global_trivialization_forces_trivial_monodromy hglob g)

end MeasurementNetMonodromy
