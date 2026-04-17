import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic

universe u v

namespace MeasurementNetClosure

/-- Minimal measurement-net placeholder for the closure architecture. -/
structure MeasurementNet where
  Region : Type u

/-- Abstract exact-sequence package at the level of communicable symmetries. -/
structure ExactSequenceData (N : MeasurementNet.{u}) where
  Gauge : Type v
  Aut : Type v
  Spacetime : Type v
  gaugeGroup : Group Gauge
  autGroup : Group Aut
  spacetimeGroup : Group Spacetime
  incl : Gauge →* Aut
  proj : Aut →* Spacetime

attribute [instance] ExactSequenceData.gaugeGroup
attribute [instance] ExactSequenceData.autGroup
attribute [instance] ExactSequenceData.spacetimeGroup

/-- Microscopic completion data used in the paper's closure conjecture. -/
structure MicroscopicCompletion (N : MeasurementNet.{u}) where
  CompletionAut : Type v
  completionGroup : Group CompletionAut
  coarseDataVisible : Prop

attribute [instance] MicroscopicCompletion.completionGroup

/-- Kernel-level closure package: communicable automorphisms descend to the coarse
net, with precisely an inert kernel lost under coarse-graining. -/
structure ClosurePackage (N : MeasurementNet.{u})
    (E : ExactSequenceData N) (C : MicroscopicCompletion N) where
  CommAut : Type v
  commGroup : Group CommAut
  inertKernel : Set CommAut
  descendsToAut : CommAut →* E.Aut
  surjective_descent : Function.Surjective descendsToAut
  kernel_is_inert :
    ∀ η : CommAut, descendsToAut η = 1 ↔ η ∈ inertKernel

attribute [instance] ClosurePackage.commGroup

/-- Abstract short exactness of the kernel-level descent statement. -/
theorem closure_short_exact
    {N : MeasurementNet.{u}} (E : ExactSequenceData N)
    (C : MicroscopicCompletion N) (K : ClosurePackage N E C) :
    Function.Surjective K.descendsToAut ∧
      ∀ η : K.CommAut, K.descendsToAut η = 1 ↔ η ∈ K.inertKernel := by
  constructor
  · exact K.surjective_descent
  · intro η
    exact K.kernel_is_inert η

/-- If a communicable automorphism is inert, it becomes trivial after descent. -/
theorem inert_acts_trivially_downstairs
    {N : MeasurementNet.{u}} (E : ExactSequenceData N)
    (C : MicroscopicCompletion N) (K : ClosurePackage N E C)
    {η : K.CommAut} (hη : η ∈ K.inertKernel) :
    K.descendsToAut η = 1 := by
  exact (K.kernel_is_inert η).mpr hη

/-- Conversely, trivial descent characterizes inert microscopic symmetry. -/
theorem trivial_descent_is_inert
    {N : MeasurementNet.{u}} (E : ExactSequenceData N)
    (C : MicroscopicCompletion N) (K : ClosurePackage N E C)
    {η : K.CommAut} (hη : K.descendsToAut η = 1) :
    η ∈ K.inertKernel := by
  exact (K.kernel_is_inert η).mp hη

/-- Abstract statement of the commuting exact-sequence diagram in the paper:
no new communicable spacetime symmetry appears upstairs once one descends along
coarse-graining. -/
structure ClosureCompatibility (N : MeasurementNet.{u})
    (E : ExactSequenceData N) (C : MicroscopicCompletion N) (K : ClosurePackage N E C) where
  upstairsSpacetime : Type v
  upstairsSpacetimeGroup : Group upstairsSpacetime
  upstairsProj : K.CommAut →* upstairsSpacetime
  spacetimeIso : upstairsSpacetime ≃* E.Spacetime
  commutes : ∀ η : K.CommAut,
    E.proj (K.descendsToAut η) = spacetimeIso (upstairsProj η)

attribute [instance] ClosureCompatibility.upstairsSpacetimeGroup

/-- Communicable spacetime symmetry is saturated by the coarse exact-sequence architecture. -/
theorem no_new_spacetime_symmetry
    {N : MeasurementNet.{u}} (E : ExactSequenceData N)
    (C : MicroscopicCompletion N) (K : ClosurePackage N E C)
    (Compat : ClosureCompatibility N E C K) :
    ∀ η : K.CommAut, E.proj (K.descendsToAut η) = Compat.spacetimeIso (Compat.upstairsProj η) := by
  intro η
  exact Compat.commutes η

end MeasurementNetClosure
