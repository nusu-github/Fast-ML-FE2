import FastMLFE2.GlobalSystem

namespace FastMLFE2

/-- One global linear equation on a fixed grid. -/
structure GlobalLevelData (h w k : Nat) where
  neighbors : Neighborhood h w k
  weightRule : WeightRule h w k
  image : GrayImage h w
  alpha : GrayImage h w

namespace GlobalLevelData

def systemMatrix {h w k : Nat} (data : GlobalLevelData h w k) :
    Matrix (GlobalBlockIdx h w) (GlobalBlockIdx h w) ℝ :=
  globalSystemMatrix data.neighbors data.weightRule data.alpha

def rhs {h w k : Nat} (data : GlobalLevelData h w k) : GlobalBlockIdx h w → ℝ :=
  globalRhs data.image data.alpha

def residual {h w k : Nat} (data : GlobalLevelData h w k) (state : GlobalState h w) :
    GlobalState h w :=
  globalLinearResidual data.neighbors data.weightRule data.image data.alpha state

def system {h w k : Nat} (data : GlobalLevelData h w k) (state : GlobalState h w) : Prop :=
  globalSystem data.neighbors data.weightRule data.image data.alpha state

theorem system_iff_residual_zero {h w k : Nat} (data : GlobalLevelData h w k)
    (state : GlobalState h w) :
    data.system state ↔ data.residual state = 0 := by
  rfl

theorem residual_eq_localResidual {h w k : Nat} (data : GlobalLevelData h w k)
    (fg bg : GrayImage h w) (px : Pixel h w) :
    data.residual (mkGlobalState fg bg) px =
      (localDataOfNeighborhood data.alpha fg bg data.neighbors data.weightRule px).localResidual
        (data.alpha px) (data.image px) (mkFBVec (fg px) (bg px)) := by
  exact globalLinearResidual_eq_localResidual data.neighbors data.weightRule
    data.image data.alpha fg bg px

theorem system_iff_forall_stationary {h w k : Nat} (data : GlobalLevelData h w k)
    (fg bg : GrayImage h w) :
    data.system (mkGlobalState fg bg) ↔
      ∀ px, (localDataOfNeighborhood data.alpha fg bg data.neighbors data.weightRule px).stationary
        (data.alpha px) (data.image px) (mkFBVec (fg px) (bg px)) := by
  exact globalSystem_iff_forall_stationary data.neighbors data.weightRule
    data.image data.alpha fg bg

theorem system_iff_forall_localSystem {h w k : Nat} (data : GlobalLevelData h w k)
    (fg bg : GrayImage h w) :
    data.system (mkGlobalState fg bg) ↔
      ∀ px, (localDataOfNeighborhood data.alpha fg bg data.neighbors data.weightRule px).localSystem
        (data.alpha px) (data.image px) (mkFBVec (fg px) (bg px)) := by
  exact globalSystem_iff_forall_localSystem data.neighbors data.weightRule
    data.image data.alpha fg bg

end GlobalLevelData

/-- Abstract residual transfer and correction prolongation between two grids. -/
structure GridTransfer (FineResidual CoarseResidual FineState CoarseState : Type*)
    [Zero FineResidual] [Zero CoarseResidual] [Zero FineState] [Zero CoarseState] where
  restrictResidual : FineResidual → CoarseResidual
  prolongCorrection : CoarseState → FineState
  restrict_zero : restrictResidual 0 = 0
  prolong_zero : prolongCorrection 0 = 0

/-- Abstract two-grid V-cycle skeleton. The coarse problem is expressed in residual form. -/
structure VCycleOps (FineData FineState FineResidual CoarseResidual CoarseState : Type*)
    [Zero FineResidual] [Zero CoarseResidual] [Zero FineState] [Zero CoarseState] where
  preSmooth : FineData → FineState → FineState
  postSmooth : FineData → FineState → FineState
  residual : FineData → FineState → FineResidual
  coarseSolve : CoarseResidual → CoarseState
  transfer : GridTransfer FineResidual CoarseResidual FineState CoarseState
  correct : FineState → FineState → FineState
  coarseSolve_zero : coarseSolve 0 = 0
  correct_zero : ∀ state, correct state 0 = state

namespace VCycleOps

variable {FineData FineState FineResidual CoarseResidual CoarseState : Type*}
variable [Zero FineResidual] [Zero CoarseResidual] [Zero FineState] [Zero CoarseState]

def vCycle (ops : VCycleOps FineData FineState FineResidual CoarseResidual CoarseState)
    (data : FineData) (state : FineState) : FineState :=
  let preState := ops.preSmooth data state
  let fineResidual := ops.residual data preState
  let coarseResidual := ops.transfer.restrictResidual fineResidual
  let coarseCorrection := ops.coarseSolve coarseResidual
  let fineCorrection := ops.transfer.prolongCorrection coarseCorrection
  let corrected := ops.correct preState fineCorrection
  ops.postSmooth data corrected

def fixedPoint (ops : VCycleOps FineData FineState FineResidual CoarseResidual CoarseState)
    (data : FineData) (state : FineState) : Prop :=
  ops.preSmooth data state = state ∧
    ops.residual data state = 0 ∧
    ops.postSmooth data state = state

theorem vCycle_eq_self_of_fixedPoint
    (ops : VCycleOps FineData FineState FineResidual CoarseResidual CoarseState)
    (data : FineData) (state : FineState)
    (hFixed : ops.fixedPoint data state) :
    ops.vCycle data state = state := by
  rcases hFixed with ⟨hPre, hResidual, hPost⟩
  simp [VCycleOps.vCycle, hPre, hResidual, hPost, ops.transfer.restrict_zero,
    ops.coarseSolve_zero, ops.transfer.prolong_zero, ops.correct_zero]

end VCycleOps

def addGlobalCorrection {h w : Nat}
    (state correction : GlobalState h w) : GlobalState h w :=
  state + correction

@[simp] theorem addGlobalCorrection_zero {h w : Nat} (state : GlobalState h w) :
    addGlobalCorrection state 0 = state := by
  funext px
  apply ext_fbVec <;> simp [addGlobalCorrection]

end FastMLFE2
