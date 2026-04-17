import Lake
open Lake DSL

package «measurement-net-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0-rc1"

lean_lib MeasurementNetExactSequence where
lean_lib MeasurementNetSplitting where
lean_lib MeasurementNetMonodromy where
lean_lib MeasurementNetModuli where
lean_lib MeasurementNetIndependence where
lean_lib MeasurementNetReconstruction where
lean_lib MeasurementNetClosure where
lean_lib MeasurementNetEnrichment where
lean_lib MeasurementNetQGObstruction where
lean_lib MeasurementNetRigidity where
lean_lib MeasurementNetAnomaly where
lean_lib MeasurementNetMonodromy2Cat where
