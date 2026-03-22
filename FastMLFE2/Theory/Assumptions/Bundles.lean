import FastMLFE2.Theory.Core.LocalEquation
import FastMLFE2.Theory.Canonical.LocalCommitments

namespace FastMLFE2.Theory.Assumptions

/-!
Explicit assumption bundles for the refounded theory kernel.
-/

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Canonical

class CoreMathAssumptions {ι : Type*} [Fintype ι]
    (ctx : LocalContext ι) : Prop where
  epsilonPos : 0 < ctx.epsilonR
  omegaNonneg : 0 ≤ ctx.omega
  alphaCenterBounded : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1
  neighborNonempty : Nonempty ι

structure AlphaAssumptions {ι : Type*} [Fintype ι] (ctx : LocalContext ι) : Prop where
  centerInUnitInterval : 0 ≤ ctx.alphaCenter ∧ ctx.alphaCenter ≤ 1
  neighborsInUnitInterval : ∀ j, 0 ≤ ctx.alphaNeighbor j ∧ ctx.alphaNeighbor j ≤ 1

inductive ChannelMode where
  | sharedMatrixAcrossRGB
  deriving DecidableEq, Repr

structure ChannelAssumptions where
  mode : ChannelMode := .sharedMatrixAcrossRGB
  deriving DecidableEq, Repr

inductive BackendScheduleVariant where
  | canonicalDeterministic
  | cpuAsyncInPlace
  | gpuJacobi
  deriving DecidableEq, Repr

structure VariantAssumptions where
  backendSchedule : BackendScheduleVariant := .canonicalDeterministic
  alternateNeighborhood : Bool := false
  deriving DecidableEq, Repr

inductive InitializationPolicy where
  | canonicalAuthored
  | zero
  | meanColor
  | resizedImage
  deriving DecidableEq, Repr

structure InitializationAssumptions where
  policy : InitializationPolicy := .canonicalAuthored
  deriving DecidableEq, Repr

structure ProjectionAssumptions where
  placement : ProjectionPlacement := .insideIteration
  deriving DecidableEq, Repr

structure HardwareAssumptions where
  vectorWidth : Nat
  warpSize : Nat
  sharedMemoryBudget : Nat
  deriving DecidableEq, Repr

def defaultInitializationAssumptions : InitializationAssumptions where
  policy := .canonicalAuthored

def defaultProjectionAssumptions : ProjectionAssumptions where
  placement := .insideIteration

def defaultHardwareAssumptions : HardwareAssumptions where
  vectorWidth := 1
  warpSize := 1
  sharedMemoryBudget := 0

end FastMLFE2.Theory.Assumptions
