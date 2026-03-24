import FastMLFE2.Canonical.Builder

namespace FastMLFE2.Canonical

open FastMLFE2.Core
open FastMLFE2.Level

namespace CanonicalPixelData

variable {κ : Type*} {η : κ → Type*} [∀ p, Fintype (η p)]

/-- Clamp every pixel state componentwise into `[0, 1]`. -/
def stateClamp01 (state : PixelState κ) : PixelState κ :=
  fun p => clamp01 (state p)

/-- One raw canonical fixed-level Jacobi step with no projection. -/
noncomputable def rawStep
    (data : CanonicalPixelData κ η)
    (state : PixelState κ) : PixelState κ :=
  data.canonicalBuilder.jacobiStep state

/-- One canonical fixed-level step with projection applied immediately. -/
noncomputable def insideClampedStep
    (data : CanonicalPixelData κ η)
    (state : PixelState κ) : PixelState κ :=
  stateClamp01 (data.rawStep state)

/-- `k` raw Jacobi steps with no intermediate projection. -/
noncomputable def rawIterate
    (data : CanonicalPixelData κ η)
    (k : Nat)
    (state : PixelState κ) : PixelState κ :=
  Nat.iterate data.rawStep k state

/-- `k` canonical steps with projection applied after every raw step. -/
noncomputable def insideClampedIterate
    (data : CanonicalPixelData κ η)
    (k : Nat)
    (state : PixelState κ) : PixelState κ :=
  Nat.iterate data.insideClampedStep k state

/-- `k` raw steps followed by a single projection at the end. -/
noncomputable def endClampedIterate
    (data : CanonicalPixelData κ η)
    (k : Nat)
    (state : PixelState κ) : PixelState κ :=
  stateClamp01 (data.rawIterate k state)

@[simp] theorem stateClamp01_apply
    (state : PixelState κ)
    (p : κ) :
    stateClamp01 state p = clamp01 (state p) := rfl

@[simp] theorem rawStep_apply
    (data : CanonicalPixelData κ η)
    (state : PixelState κ)
    (p : κ) :
    data.rawStep state p = data.canonicalBuilder.jacobiStep state p := rfl

@[simp] theorem insideClampedStep_apply
    (data : CanonicalPixelData κ η)
    (state : PixelState κ)
    (p : κ) :
    data.insideClampedStep state p = clamp01 (data.rawStep state p) := rfl

@[simp] theorem rawIterate_zero
    (data : CanonicalPixelData κ η)
    (state : PixelState κ) :
    data.rawIterate 0 state = state := rfl

@[simp] theorem insideClampedIterate_zero
    (data : CanonicalPixelData κ η)
    (state : PixelState κ) :
    data.insideClampedIterate 0 state = state := rfl

@[simp] theorem rawIterate_succ
    (data : CanonicalPixelData κ η)
    (k : Nat)
    (state : PixelState κ) :
    data.rawIterate (k + 1) state = data.rawIterate k (data.rawStep state) := by
  simp [rawIterate, Function.iterate_succ_apply]

@[simp] theorem insideClampedIterate_succ
    (data : CanonicalPixelData κ η)
    (k : Nat)
    (state : PixelState κ) :
    data.insideClampedIterate (k + 1) state =
      data.insideClampedIterate k (data.insideClampedStep state) := by
  simp [insideClampedIterate, Function.iterate_succ_apply]

end CanonicalPixelData

def ClampPlacementCounterexampleEta : PUnit → Type := fun _ => Fin 1

instance clampPlacementCounterexampleEtaInst
    (p : PUnit) : Fintype (ClampPlacementCounterexampleEta p) := by
  change Fintype (Fin 1)
  infer_instance

noncomputable def clampPlacementCounterexampleData :
    CanonicalPixelData PUnit ClampPlacementCounterexampleEta where
  alpha := fun _ => (1 : ℝ) / 4
  image := fun _ => 0
  neighborPixel := fun _ _ => PUnit.unit
  epsilonR := (1 : ℝ) / 8
  omega := (1 : ℝ) / 2

noncomputable def clampPlacementCounterexampleState0 : PixelState PUnit :=
  fun _ => mkLocalUnknown 0 1

noncomputable def clampPlacementCounterexampleRaw1 : PixelState PUnit :=
  CanonicalPixelData.rawIterate
    (κ := PUnit)
    (η := ClampPlacementCounterexampleEta)
    clampPlacementCounterexampleData
    1
    clampPlacementCounterexampleState0

noncomputable def clampPlacementCounterexampleInside1 : PixelState PUnit :=
  CanonicalPixelData.insideClampedIterate
    (κ := PUnit)
    (η := ClampPlacementCounterexampleEta)
    clampPlacementCounterexampleData
    1
    clampPlacementCounterexampleState0

noncomputable def clampPlacementCounterexampleRaw2 : PixelState PUnit :=
  CanonicalPixelData.rawIterate
    (κ := PUnit)
    (η := ClampPlacementCounterexampleEta)
    clampPlacementCounterexampleData
    2
    clampPlacementCounterexampleState0

noncomputable def clampPlacementCounterexampleInside2 : PixelState PUnit :=
  CanonicalPixelData.insideClampedIterate
    (κ := PUnit)
    (η := ClampPlacementCounterexampleEta)
    clampPlacementCounterexampleData
    2
    clampPlacementCounterexampleState0

noncomputable def clampPlacementCounterexampleEnd2 : PixelState PUnit :=
  CanonicalPixelData.endClampedIterate
    (κ := PUnit)
    (η := ClampPlacementCounterexampleEta)
    clampPlacementCounterexampleData
    2
    clampPlacementCounterexampleState0

end FastMLFE2.Canonical
