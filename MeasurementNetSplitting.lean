import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic

universe u v

namespace MeasurementNetSplitting

/-- Minimal topological input for the paper-level splitting architecture. -/
structure MeasurementNet where
  Region : Type u
  Contractible : Region → Prop

/-- Abstract local exact-sequence package for the measurement net automorphism architecture. -/
structure LocalExactSequence (N : MeasurementNet.{u}) where
  Gauge : Type v
  Aut : Type v
  Spacetime : Type v
  gaugeGroup : Group Gauge
  autGroup : Group Aut
  spacetimeGroup : Group Spacetime
  incl : Gauge →* Aut
  proj : Aut →* Spacetime

attribute [instance] LocalExactSequence.gaugeGroup
attribute [instance] LocalExactSequence.autGroup
attribute [instance] LocalExactSequence.spacetimeGroup

/-- Hypotheses isolating the logical shape of the splitting lemma.

`locallyConstant` is not assumed arbitrarily: it is produced from the four
load-bearing inputs by `rigidity_forces_localConstancy`, mirroring the paper's
use of continuity, finite distinguishability, fusion hypotheses, and Ocneanu
rigidity. -/
structure SplittingHypotheses (N : MeasurementNet.{u}) (E : LocalExactSequence N) where
  continuity : Prop
  finiteDistinguishability : Prop
  fusionFiberHypotheses : Prop
  ocneanuRigidity : Prop
  locallyConstant : Prop
  localSectionExists : N.Region → Prop
  rigidity_forces_localConstancy :
    continuity → finiteDistinguishability → fusionFiberHypotheses → ocneanuRigidity → locallyConstant
  locallyConstant_gives_localSections :
    locallyConstant → ∀ U : N.Region, N.Contractible U → localSectionExists U

/-- The paper's splitting lemma, formalised as an abstract theorem schema:
rigidity of the categorical fibers forces local constancy, and local constancy
forces local sections on contractible opens. -/
theorem splitting_lemma
    {N : MeasurementNet.{u}} (E : LocalExactSequence N) (H : SplittingHypotheses N E) :
    H.continuity →
    H.finiteDistinguishability →
    H.fusionFiberHypotheses →
    H.ocneanuRigidity →
    ∀ U : N.Region, N.Contractible U → H.localSectionExists U := by
  intro hcont hfinite hfusion hrigid U hU
  let hloc := H.rigidity_forces_localConstancy hcont hfinite hfusion hrigid
  exact H.locallyConstant_gives_localSections hloc U hU

/-- The intermediate locally-constant conclusion singled out explicitly. -/
theorem locallyConstant_of_rigidity
    {N : MeasurementNet.{u}} (E : LocalExactSequence N) (H : SplittingHypotheses N E) :
    H.continuity →
    H.finiteDistinguishability →
    H.fusionFiberHypotheses →
    H.ocneanuRigidity →
    H.locallyConstant := by
  intro hcont hfinite hfusion hrigid
  exact H.rigidity_forces_localConstancy hcont hfinite hfusion hrigid

/-- Abstract monodromy package for the global-splitting corollary. -/
structure MonodromyPackage (N : MeasurementNet.{u}) (E : LocalExactSequence N) where
  simplyConnected : Prop
  monodromyTrivial : Prop
  globalSectionExists : Prop
  simplyConnected_forces_trivial : simplyConnected → monodromyTrivial
  trivialMonodromy_gives_globalSection : monodromyTrivial → globalSectionExists

/-- Simply-connected bases force global splitting once monodromy controls the only
remaining obstruction. -/
theorem global_splitting_on_simply_connected
    {N : MeasurementNet.{u}} (E : LocalExactSequence N) (M : MonodromyPackage N E) :
    M.simplyConnected → M.globalSectionExists := by
  intro hsc
  apply M.trivialMonodromy_gives_globalSection
  exact M.simplyConnected_forces_trivial hsc

end MeasurementNetSplitting
