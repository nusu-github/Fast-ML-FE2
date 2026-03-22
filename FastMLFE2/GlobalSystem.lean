import FastMLFE2.ConcreteImage
import FastMLFE2.NormalEquation

namespace FastMLFE2

/-- Flattened `(pixel, foreground/background)` index for the global block system. -/
abbrev GlobalBlockIdx (h w : Nat) := Pixel h w × FBIdx

/-- Global foreground/background state as one `FBVec` per pixel. -/
abbrev GlobalState (h w : Nat) := Pixel h w → FBVec

def mkGlobalState {h w : Nat} (fg bg : GrayImage h w) : GlobalState h w :=
  fun px => mkFBVec (fg px) (bg px)

def foregroundImage {h w : Nat} (state : GlobalState h w) : GrayImage h w :=
  fun px => foreground (state px)

def backgroundImage {h w : Nat} (state : GlobalState h w) : GrayImage h w :=
  fun px => background (state px)

def flattenState {h w : Nat} (state : GlobalState h w) : GlobalBlockIdx h w → ℝ
  | (px, i) => state px i

def unflattenState {h w : Nat} (v : GlobalBlockIdx h w → ℝ) : GlobalState h w :=
  fun px => mkFBVec (v (px, 0)) (v (px, 1))

@[simp] theorem foregroundImage_mkGlobalState {h w : Nat} (fg bg : GrayImage h w) :
    foregroundImage (mkGlobalState fg bg) = fg := by
  funext px
  simp [foregroundImage, mkGlobalState]

@[simp] theorem backgroundImage_mkGlobalState {h w : Nat} (fg bg : GrayImage h w) :
    backgroundImage (mkGlobalState fg bg) = bg := by
  funext px
  simp [backgroundImage, mkGlobalState]

@[simp] theorem flattenState_foreground {h w : Nat} (state : GlobalState h w) (px : Pixel h w) :
    flattenState state (px, 0) = foreground (state px) := by
  simp [flattenState, foreground]

@[simp] theorem flattenState_background {h w : Nat} (state : GlobalState h w) (px : Pixel h w) :
    flattenState state (px, 1) = background (state px) := by
  simp [flattenState, background]

@[simp] theorem flattenState_unflattenState {h w : Nat} (v : GlobalBlockIdx h w → ℝ) :
    flattenState (unflattenState v) = v := by
  funext idx
  rcases idx with ⟨px, i⟩
  fin_cases i <;> simp [flattenState, unflattenState, mkFBVec]

@[simp] theorem unflattenState_flattenState {h w : Nat} (state : GlobalState h w) :
    unflattenState (flattenState state) = state := by
  funext px
  apply ext_fbVec <;> simp [unflattenState, flattenState, foreground, background, mkFBVec]

/-- Aggregated edge weight from `px` to `py`, summing duplicate clamped neighbors if needed. -/
def edgeWeight {h w k : Nat} (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (alpha : GrayImage h w) (px py : Pixel h w) : ℝ :=
  ∑ t, if neighborPixel neighbors px t = py then
    weightRule alpha px t (neighborPixel neighbors px t)
  else
    0

def adjacencyMatrix {h w k : Nat} (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (alpha : GrayImage h w) : Matrix (Pixel h w) (Pixel h w) ℝ :=
  fun px py => edgeWeight neighbors weightRule alpha px py

def pixelTotalWeight {h w k : Nat} (neighbors : Neighborhood h w k)
    (weightRule : WeightRule h w k) (alpha : GrayImage h w) (px : Pixel h w) : ℝ :=
  ∑ py, edgeWeight neighbors weightRule alpha px py

/-- Weighted graph Laplacian `L_w = D_s - W` on the pixel graph. -/
def weightedLaplacian {h w k : Nat} (neighbors : Neighborhood h w k)
    (weightRule : WeightRule h w k) (alpha : GrayImage h w) :
    Matrix (Pixel h w) (Pixel h w) ℝ :=
  Matrix.diagonal (pixelTotalWeight neighbors weightRule alpha) -
    adjacencyMatrix neighbors weightRule alpha

def betaImage {h w : Nat} (alpha : GrayImage h w) : GrayImage h w :=
  fun px => 1 - alpha px

def globalSystemMatrix {h w k : Nat} (neighbors : Neighborhood h w k)
    (weightRule : WeightRule h w k) (alpha : GrayImage h w) :
    Matrix (GlobalBlockIdx h w) (GlobalBlockIdx h w) ℝ
  | (px, 0), (py, 0) =>
      weightedLaplacian neighbors weightRule alpha px py +
        if px = py then (alpha px) ^ 2 else 0
  | (px, 0), (py, 1) =>
      if px = py then alpha px * betaImage alpha px else 0
  | (px, 1), (py, 0) =>
      if px = py then alpha px * betaImage alpha px else 0
  | (px, 1), (py, 1) =>
      weightedLaplacian neighbors weightRule alpha px py +
        if px = py then (betaImage alpha px) ^ 2 else 0

def globalRhs {h w : Nat} (image alpha : GrayImage h w) : GlobalBlockIdx h w → ℝ
  | (px, 0) => alpha px * image px
  | (px, 1) => betaImage alpha px * image px

/-- Global residual in image form, i.e. one `FBVec` residual per pixel. -/
def globalLinearResidual {h w k : Nat} (neighbors : Neighborhood h w k)
    (weightRule : WeightRule h w k) (image alpha : GrayImage h w)
    (state : GlobalState h w) : GlobalState h w :=
  fun px =>
    let β := betaImage alpha px
    mkFBVec
      ((weightedLaplacian neighbors weightRule alpha).mulVec (foregroundImage state) px +
        (alpha px) ^ 2 * foreground (state px) +
        alpha px * β * background (state px) -
        alpha px * image px)
      ((weightedLaplacian neighbors weightRule alpha).mulVec (backgroundImage state) px +
        alpha px * β * foreground (state px) +
        β ^ 2 * background (state px) -
        β * image px)

/-- Pointwise zero global residual, equivalent to solving the global linear system. -/
def globalSystem {h w k : Nat} (neighbors : Neighborhood h w k)
    (weightRule : WeightRule h w k) (image alpha : GrayImage h w)
    (state : GlobalState h w) : Prop :=
  globalLinearResidual neighbors weightRule image alpha state = 0

theorem sum_edgeWeight_mul {h w k : Nat} (neighbors : Neighborhood h w k)
    (weightRule : WeightRule h w k) (alpha : GrayImage h w) (px : Pixel h w)
    (f : Pixel h w → ℝ) :
    ∑ py, edgeWeight neighbors weightRule alpha px py * f py =
      ∑ t,
        weightRule alpha px t (neighborPixel neighbors px t) *
          f (neighborPixel neighbors px t) := by
  classical
  simp_rw [edgeWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro t ht
  simp

theorem pixelTotalWeight_eq_weightSum {h w k : Nat} (neighbors : Neighborhood h w k)
    (weightRule : WeightRule h w k) (alpha : GrayImage h w) (px : Pixel h w) :
    pixelTotalWeight neighbors weightRule alpha px =
      ∑ t, weightRule alpha px t (neighborPixel neighbors px t) := by
  classical
  simpa [pixelTotalWeight] using
    (sum_edgeWeight_mul neighbors weightRule alpha px (fun _ => (1 : ℝ)))

theorem weightedLaplacian_mulVec_eq {h w k : Nat} (neighbors : Neighborhood h w k)
    (weightRule : WeightRule h w k) (alpha : GrayImage h w)
    (x : Pixel h w → ℝ) (px : Pixel h w) :
    (weightedLaplacian neighbors weightRule alpha).mulVec x px =
      ∑ t, weightRule alpha px t (neighborPixel neighbors px t) *
        (x px - x (neighborPixel neighbors px t)) := by
  classical
  have hdiag :
      (Matrix.diagonal (pixelTotalWeight neighbors weightRule alpha)).mulVec x px =
        pixelTotalWeight neighbors weightRule alpha px * x px := by
    simpa using
      (Matrix.mulVec_diagonal (pixelTotalWeight neighbors weightRule alpha) x px)
  have hadj :
      (adjacencyMatrix neighbors weightRule alpha).mulVec x px =
        ∑ py, edgeWeight neighbors weightRule alpha px py * x py := by
    simp [adjacencyMatrix, Matrix.mulVec, dotProduct]
  calc
    (weightedLaplacian neighbors weightRule alpha).mulVec x px =
        pixelTotalWeight neighbors weightRule alpha px * x px -
          ∑ py, edgeWeight neighbors weightRule alpha px py * x py := by
          rw [weightedLaplacian, Matrix.sub_mulVec, Pi.sub_apply, hdiag, hadj]
    _ =
        (∑ t, weightRule alpha px t (neighborPixel neighbors px t)) * x px -
          ∑ t, weightRule alpha px t (neighborPixel neighbors px t) *
            x (neighborPixel neighbors px t) := by
          rw [pixelTotalWeight_eq_weightSum, sum_edgeWeight_mul]
    _ =
        ∑ t, weightRule alpha px t (neighborPixel neighbors px t) * x px -
          ∑ t, weightRule alpha px t (neighborPixel neighbors px t) *
            x (neighborPixel neighbors px t) := by
          rw [Finset.sum_mul]
    _ = ∑ t, (weightRule alpha px t (neighborPixel neighbors px t) * x px -
          weightRule alpha px t (neighborPixel neighbors px t) *
            x (neighborPixel neighbors px t)) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ t, weightRule alpha px t (neighborPixel neighbors px t) *
        (x px - x (neighborPixel neighbors px t)) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          ring

set_option linter.flexible false in
theorem globalLinearResidual_eq_localResidual {h w k : Nat}
    (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (image alpha fg bg : GrayImage h w) (px : Pixel h w) :
    globalLinearResidual neighbors weightRule image alpha (mkGlobalState fg bg) px =
      (localDataOfNeighborhood alpha fg bg neighbors weightRule px).localResidual
        (alpha px) (image px) (mkFBVec (fg px) (bg px)) := by
  apply ext_fbVec
  · simp [globalLinearResidual, LocalData.localResidual, LocalData.halfGradient,
      weightedLaplacian_mulVec_eq, mkGlobalState, betaImage, localDataOfNeighborhood,
      compositingResidual_eq, foreground, background, mkFBVec]
    have hsum :
        ∑ t, weightRule alpha px t (neighborPixel neighbors px t) *
            (fg px - fg (neighborPixel neighbors px t)) =
          ∑ t,
            (fg px * weightRule alpha px t (neighborPixel neighbors px t) -
              weightRule alpha px t (neighborPixel neighbors px t) *
                fg (neighborPixel neighbors px t)) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      ring
    rw [hsum]
    have hmain :
        alpha px ^ 2 * fg px + alpha px * (1 - alpha px) * bg px - alpha px * image px =
          alpha px * (alpha px * fg px + (1 - alpha px) * bg px - image px) := by
      ring
    let s : ℝ :=
      ∑ t,
        (fg px * weightRule alpha px t (neighborPixel neighbors px t) -
          weightRule alpha px t (neighborPixel neighbors px t) *
            fg (neighborPixel neighbors px t))
    have hs : s + (alpha px ^ 2 * fg px + alpha px * (1 - alpha px) * bg px - alpha px * image px) =
        s + alpha px * (alpha px * fg px + (1 - alpha px) * bg px - image px) := by
      exact congrArg (fun z : ℝ => s + z) hmain
    simpa only [s, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs
  · simp [globalLinearResidual, LocalData.localResidual, LocalData.halfGradient,
      weightedLaplacian_mulVec_eq, mkGlobalState, betaImage, localDataOfNeighborhood,
      compositingResidual_eq, foreground, background, mkFBVec]
    have hsum :
        ∑ t, weightRule alpha px t (neighborPixel neighbors px t) *
            (bg px - bg (neighborPixel neighbors px t)) =
          ∑ t,
            (bg px * weightRule alpha px t (neighborPixel neighbors px t) -
              weightRule alpha px t (neighborPixel neighbors px t) *
                bg (neighborPixel neighbors px t)) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      ring
    rw [hsum]
    have hmain :
        alpha px * (1 - alpha px) * fg px + (1 - alpha px) ^ 2 * bg px -
            (1 - alpha px) * image px =
          (1 - alpha px) * (alpha px * fg px + (1 - alpha px) * bg px - image px) := by
      ring
    let s : ℝ :=
      ∑ t,
        (bg px * weightRule alpha px t (neighborPixel neighbors px t) -
          weightRule alpha px t (neighborPixel neighbors px t) *
            bg (neighborPixel neighbors px t))
    have hs :
        s + (alpha px * (1 - alpha px) * fg px + (1 - alpha px) ^ 2 * bg px -
          (1 - alpha px) * image px) =
        s + (1 - alpha px) * (alpha px * fg px + (1 - alpha px) * bg px - image px) := by
      exact congrArg (fun z : ℝ => s + z) hmain
    simpa only [s, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs

theorem globalSystem_iff_forall_stationary {h w k : Nat}
    (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (image alpha fg bg : GrayImage h w) :
    globalSystem neighbors weightRule image alpha (mkGlobalState fg bg) ↔
      ∀ px, (localDataOfNeighborhood alpha fg bg neighbors weightRule px).stationary
        (alpha px) (image px) (mkFBVec (fg px) (bg px)) := by
  constructor
  · intro hglobal px
    have hres :
        globalLinearResidual neighbors weightRule image alpha (mkGlobalState fg bg) px = 0 := by
      simpa [globalSystem] using congrArg (fun s => s px) hglobal
    have hlocal :
        (localDataOfNeighborhood alpha fg bg neighbors weightRule px).localResidual
          (alpha px) (image px) (mkFBVec (fg px) (bg px)) = 0 := by
      simpa [globalLinearResidual_eq_localResidual
        (neighbors := neighbors) (weightRule := weightRule)
        (image := image) (alpha := alpha) (fg := fg) (bg := bg) (px := px)] using hres
    simpa [LocalData.stationary, LocalData.localResidual] using hlocal
  · intro hstationary
    funext px
    have hlocal :
        (localDataOfNeighborhood alpha fg bg neighbors weightRule px).localResidual
          (alpha px) (image px) (mkFBVec (fg px) (bg px)) = 0 := by
      simpa [LocalData.stationary, LocalData.localResidual] using hstationary px
    simpa [globalLinearResidual_eq_localResidual
      (neighbors := neighbors) (weightRule := weightRule)
      (image := image) (alpha := alpha) (fg := fg) (bg := bg) (px := px)] using hlocal

theorem globalSystem_iff_forall_localSystem {h w k : Nat}
    (neighbors : Neighborhood h w k) (weightRule : WeightRule h w k)
    (image alpha fg bg : GrayImage h w) :
    globalSystem neighbors weightRule image alpha (mkGlobalState fg bg) ↔
      ∀ px, (localDataOfNeighborhood alpha fg bg neighbors weightRule px).localSystem
        (alpha px) (image px) (mkFBVec (fg px) (bg px)) := by
  rw [globalSystem_iff_forall_stationary]
  constructor
  · intro h px
    exact ((localDataOfNeighborhood alpha fg bg neighbors weightRule px).stationary_iff_localSystem
      (α := alpha px) (image := image px) (g := mkFBVec (fg px) (bg px))).mp (h px)
  · intro h px
    exact ((localDataOfNeighborhood alpha fg bg neighbors weightRule px).stationary_iff_localSystem
      (α := alpha px) (image := image px) (g := mkFBVec (fg px) (bg px))).mpr (h px)

end FastMLFE2
