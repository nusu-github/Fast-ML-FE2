import FastMLFE2.FixedPrecision.Cost
import FastMLFE2.Canonical.MultilevelSchedule

namespace FastMLFE2.FixedPrecision

open FastMLFE2.Canonical

abbrev FixedGridState (cfg : FixedFormat) (h w : Nat) := Pixel h w → FixedUnknown cfg

abbrev FixedGridBuilder (cfg : FixedFormat) (h w : Nat) :=
  FixedLocalContextBuilder cfg (Pixel h w) (fun p => ValidDir p)

structure FixedLevelSpec where
  height : Nat
  width : Nat
  iterations : Nat
  heightPos : 0 < height
  widthPos : 0 < width
  deriving Repr

abbrev SomeFixedGridState (cfg : FixedFormat) :=
  Σ spec : FixedLevelSpec, FixedGridState cfg spec.height spec.width

structure FixedGridBuilderFamily (cfg : FixedFormat) where
  builder : (h w : Nat) → FixedGridBuilder cfg h w

noncomputable def fullyFixedNearestNeighborResize
    {cfg : FixedFormat} {hSrc wSrc hDst wDst : Nat}
    [Fact (0 < hSrc)] [Fact (0 < wSrc)]
    (state : FixedGridState cfg hSrc wSrc) : FixedGridState cfg hDst wDst :=
  nearestNeighborResize (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst) (wDst := wDst) state

@[simp] theorem fullyFixedNearestNeighborResize_apply
    {cfg : FixedFormat} {hSrc wSrc hDst wDst : Nat}
    [Fact (0 < hSrc)] [Fact (0 < wSrc)]
    (state : FixedGridState cfg hSrc wSrc)
    (p : Pixel hDst wDst) :
    fullyFixedNearestNeighborResize (cfg := cfg) (hSrc := hSrc) (wSrc := wSrc)
      (hDst := hDst) (wDst := wDst) state p =
      state (nearestNeighborPixel (hSrc := hSrc) (wSrc := wSrc) (hDst := hDst) (wDst := wDst) p) :=
  nearestNeighborResize_apply state p

@[simp] theorem fullyFixedNearestNeighborResize_self
    {cfg : FixedFormat} {h w : Nat}
    [Fact (0 < h)] [Fact (0 < w)]
    (state : FixedGridState cfg h w) :
    fullyFixedNearestNeighborResize (cfg := cfg) (hSrc := h) (wSrc := w) (hDst := h) (wDst := w)
      state = state := by
  simpa [fullyFixedNearestNeighborResize] using
    (nearestNeighborResize_self (h := h) (w := w) state)

inductive CheckerColor where
  | red
  | black
  deriving DecidableEq, Repr

def pixelColor {h w : Nat} (p : Pixel h w) : CheckerColor :=
  if (p.1.1 + p.2.1) % 2 = 0 then .red else .black

@[simp] theorem pixelColor_red_iff {h w : Nat} (p : Pixel h w) :
    pixelColor p = .red ↔ (p.1.1 + p.2.1) % 2 = 0 := by
  unfold pixelColor
  by_cases hparity : (p.1.1 + p.2.1) % 2 = 0
  · simp [hparity]
  · simp [hparity]

@[simp] theorem pixelColor_black_iff {h w : Nat} (p : Pixel h w) :
    pixelColor p = .black ↔ ¬ (p.1.1 + p.2.1) % 2 = 0 := by
  unfold pixelColor
  by_cases hparity : (p.1.1 + p.2.1) % 2 = 0
  · simp [hparity]
  · simp [hparity]

@[simp] theorem pixelColor_not_black_of_red {h w : Nat} (p : Pixel h w)
    (hRed : pixelColor p = .red) :
    pixelColor p ≠ .black := by
  rw [hRed]
  decide

@[simp] theorem pixelColor_not_red_of_black {h w : Nat} (p : Pixel h w)
    (hBlack : pixelColor p = .black) :
    pixelColor p ≠ .red := by
  rw [hBlack]
  decide

namespace FixedGridBuilder

variable {cfg : FixedFormat} {h w : Nat}

noncomputable def fullyFixedRedBlackHalfStep
    (builder : FixedGridBuilder cfg h w)
    (color : CheckerColor)
    (state : FixedGridState cfg h w) : FixedGridState cfg h w :=
  fun p =>
    if pixelColor p = color then
      builder.fullyFixedJacobiUpdateAt state p
    else
      state p

noncomputable def fullyFixedRedBlackSweep
    (builder : FixedGridBuilder cfg h w)
    (state : FixedGridState cfg h w) : FixedGridState cfg h w :=
  let redStep := builder.fullyFixedRedBlackHalfStep .red state
  builder.fullyFixedRedBlackHalfStep .black redStep

noncomputable def fullyFixedRedBlackIterate
    (builder : FixedGridBuilder cfg h w)
    (n : Nat)
    (state : FixedGridState cfg h w) : FixedGridState cfg h w :=
  Nat.iterate builder.fullyFixedRedBlackSweep n state

@[simp] theorem fullyFixedRedBlackHalfStep_apply_selected
    (builder : FixedGridBuilder cfg h w)
    (color : CheckerColor)
    (state : FixedGridState cfg h w)
    (p : Pixel h w)
    (hColor : pixelColor p = color) :
    builder.fullyFixedRedBlackHalfStep color state p =
      builder.fullyFixedJacobiUpdateAt state p := by
  simp [fullyFixedRedBlackHalfStep, hColor]

@[simp] theorem fullyFixedRedBlackHalfStep_apply_unselected
    (builder : FixedGridBuilder cfg h w)
    (color : CheckerColor)
    (state : FixedGridState cfg h w)
    (p : Pixel h w)
    (hColor : pixelColor p ≠ color) :
    builder.fullyFixedRedBlackHalfStep color state p = state p := by
  simp [fullyFixedRedBlackHalfStep, hColor]

theorem fullyFixedRedBlackHalfStep_eq_self_of_jacobiFixed
    (builder : FixedGridBuilder cfg h w)
    (color : CheckerColor)
    (state : FixedGridState cfg h w)
    (hFix : builder.fullyFixedJacobiStep state = state) :
    builder.fullyFixedRedBlackHalfStep color state = state := by
  funext p
  by_cases hColor : pixelColor p = color
  · have hp := congrArg (fun s => s p) hFix
    simp [FixedLocalContextBuilder.fullyFixedJacobiStep, fullyFixedRedBlackHalfStep, hColor] at hp ⊢
    exact hp
  · simp [fullyFixedRedBlackHalfStep, hColor]

theorem fullyFixedRedBlackSweep_eq_self_of_jacobiFixed
    (builder : FixedGridBuilder cfg h w)
    (state : FixedGridState cfg h w)
    (hFix : builder.fullyFixedJacobiStep state = state) :
    builder.fullyFixedRedBlackSweep state = state := by
  unfold fullyFixedRedBlackSweep
  rw [fullyFixedRedBlackHalfStep_eq_self_of_jacobiFixed builder .red state hFix]
  exact fullyFixedRedBlackHalfStep_eq_self_of_jacobiFixed builder .black state hFix

theorem redHalfStep_eq_self_of_sweepFixed
    (builder : FixedGridBuilder cfg h w)
    (state : FixedGridState cfg h w)
    (hSweep : builder.fullyFixedRedBlackSweep state = state) :
    builder.fullyFixedRedBlackHalfStep .red state = state := by
  funext p
  by_cases hRed : pixelColor p = .red
  · have hp := congrArg (fun s => s p) hSweep
    simp [fullyFixedRedBlackSweep, fullyFixedRedBlackHalfStep, hRed,
      pixelColor_not_black_of_red p hRed] at hp ⊢
    exact hp
  · simp [fullyFixedRedBlackHalfStep, hRed]

theorem fullyFixedJacobi_eq_self_of_redBlackSweep_fixed
    (builder : FixedGridBuilder cfg h w)
    (state : FixedGridState cfg h w)
    (hSweep : builder.fullyFixedRedBlackSweep state = state) :
    builder.fullyFixedJacobiStep state = state := by
  have hRedHalf : builder.fullyFixedRedBlackHalfStep .red state = state :=
    redHalfStep_eq_self_of_sweepFixed builder state hSweep
  have hBlackHalf : builder.fullyFixedRedBlackHalfStep .black state = state := by
    unfold fullyFixedRedBlackSweep at hSweep
    rw [hRedHalf] at hSweep
    exact hSweep
  funext p
  by_cases hRed : pixelColor p = .red
  · have hp := congrArg (fun s => s p) hRedHalf
    simp [FixedLocalContextBuilder.fullyFixedJacobiStep, fullyFixedRedBlackHalfStep, hRed] at hp ⊢
    exact hp
  · have hBlack : pixelColor p = .black := by
      cases hColor : pixelColor p <;> simp_all
    have hp := congrArg (fun s => s p) hBlackHalf
    simp [FixedLocalContextBuilder.fullyFixedJacobiStep, fullyFixedRedBlackHalfStep, hBlack] at hp ⊢
    exact hp

@[simp] theorem fullyFixedRedBlackIterate_zero
    (builder : FixedGridBuilder cfg h w)
    (state : FixedGridState cfg h w) :
    builder.fullyFixedRedBlackIterate 0 state = state := rfl

@[simp] theorem fullyFixedRedBlackIterate_succ
    (builder : FixedGridBuilder cfg h w)
    (n : Nat)
    (state : FixedGridState cfg h w) :
    builder.fullyFixedRedBlackIterate (n + 1) state =
      builder.fullyFixedRedBlackIterate n (builder.fullyFixedRedBlackSweep state) := by
  simp [fullyFixedRedBlackIterate, Function.iterate_succ_apply]

theorem fullyFixedLevelRun_add
    (builder : FixedGridBuilder cfg h w)
    (state : FixedGridState cfg h w)
    (n₁ n₂ : Nat) :
    builder.fullyFixedRedBlackIterate n₂ (builder.fullyFixedRedBlackIterate n₁ state) =
      builder.fullyFixedRedBlackIterate (n₁ + n₂) state := by
  have hIter := congrArg (fun f => f state) (Function.iterate_add builder.fullyFixedRedBlackSweep n₂ n₁)
  rw [Nat.add_comm]
  simpa [fullyFixedRedBlackIterate] using hIter.symm

end FixedGridBuilder

namespace FixedLevelSpec

def numPixels (spec : FixedLevelSpec) : Nat :=
  spec.height * spec.width

end FixedLevelSpec

noncomputable def resizeSomeGridState
    {cfg : FixedFormat}
    (target : FixedLevelSpec)
    (state : SomeFixedGridState cfg) : FixedGridState cfg target.height target.width := by
  rcases state with ⟨source, sourceState⟩
  letI : Fact (0 < source.height) := ⟨source.heightPos⟩
  letI : Fact (0 < source.width) := ⟨source.widthPos⟩
  exact fullyFixedNearestNeighborResize
    (cfg := cfg) (hSrc := source.height) (wSrc := source.width)
    (hDst := target.height) (wDst := target.width) sourceState

noncomputable def fullyFixedMultilevelStep
    {cfg : FixedFormat}
    (family : FixedGridBuilderFamily cfg)
    (target : FixedLevelSpec)
    (state : SomeFixedGridState cfg) : SomeFixedGridState cfg :=
  let resized := resizeSomeGridState target state
  let builder := family.builder target.height target.width
  ⟨target, builder.fullyFixedRedBlackIterate target.iterations resized⟩

noncomputable def fullyFixedMultilevelRun
    {cfg : FixedFormat}
    (family : FixedGridBuilderFamily cfg)
    (seed : SomeFixedGridState cfg)
    (levels : List FixedLevelSpec) : SomeFixedGridState cfg :=
  levels.foldl (fun state target => fullyFixedMultilevelStep family target state) seed

def resizeCost
    (model : WeightedCostModel)
    (spec : FixedLevelSpec) : ℚ :=
  (spec.numPixels : ℚ) * (model.weight .lookup + model.weight .quantize)

def redBlackSweepCost
    {cfg : FixedFormat} {h w : Nat}
    (model : WeightedCostModel)
    (builder : FixedGridBuilder cfg h w)
    (state : FixedGridState cfg h w) : ℚ :=
  jacobiStepCost model builder state

noncomputable def multilevelStepCost
    {cfg : FixedFormat}
    (model : WeightedCostModel)
    (family : FixedGridBuilderFamily cfg)
    (target : FixedLevelSpec)
    (state : SomeFixedGridState cfg) : ℚ :=
  let resized := resizeSomeGridState target state
  let builder := family.builder target.height target.width
  resizeCost model target + target.iterations * redBlackSweepCost model builder resized

noncomputable def multilevelCostAux
    {cfg : FixedFormat}
    (model : WeightedCostModel)
    (family : FixedGridBuilderFamily cfg)
    (state : SomeFixedGridState cfg)
    (levels : List FixedLevelSpec) : ℚ :=
  match levels with
  | [] => 0
  | target :: rest =>
      multilevelStepCost model family target state +
        multilevelCostAux model family (fullyFixedMultilevelStep family target state) rest

noncomputable def multilevelCost
    {cfg : FixedFormat}
    (model : WeightedCostModel)
    (family : FixedGridBuilderFamily cfg)
    (seed : SomeFixedGridState cfg)
    (levels : List FixedLevelSpec) : ℚ :=
  multilevelCostAux model family seed levels

def resizeErrorBudget (cfg : FixedFormat) : ℚ :=
  1 / cfg.scale

def levelErrorBudget (cfg : FixedFormat) : ℚ :=
  coefficientErrorBudget cfg + resizeErrorBudget cfg

def multilevelErrorBudget (cfg : FixedFormat) (levels : List FixedLevelSpec) : ℚ :=
  levels.length * levelErrorBudget cfg

def AcceptableFixedMultilevelFormat
    {cfg : FixedFormat}
    (model : WeightedCostModel)
    (family : FixedGridBuilderFamily cfg)
    (seed : SomeFixedGridState cfg)
    (levels : List FixedLevelSpec)
    (errorBudget referenceBudget : ℚ) : Prop :=
  multilevelErrorBudget cfg levels ≤ errorBudget ∧
    multilevelCost model family seed levels ≤ referenceBudget

theorem resizeCost_nonneg
    (model : WeightedCostModel)
    (spec : FixedLevelSpec) :
    0 ≤ resizeCost model spec := by
  have h := model.nonneg
  simp [resizeCost]
  nlinarith [h .lookup, h .quantize]

theorem multilevelStepCost_nonneg
    {cfg : FixedFormat}
    (model : WeightedCostModel)
    (family : FixedGridBuilderFamily cfg)
    (target : FixedLevelSpec)
    (state : SomeFixedGridState cfg) :
    0 ≤ multilevelStepCost model family target state := by
  have hResize := resizeCost_nonneg model target
  let resized := resizeSomeGridState target state
  let builder := family.builder target.height target.width
  have hSweep : 0 ≤ redBlackSweepCost model builder resized := jacobiStepCost_nonneg model builder resized
  simp [multilevelStepCost]
  nlinarith

theorem multilevelCost_nonneg
    {cfg : FixedFormat}
    (model : WeightedCostModel)
    (family : FixedGridBuilderFamily cfg)
    (seed : SomeFixedGridState cfg)
    (levels : List FixedLevelSpec) :
    0 ≤ multilevelCost model family seed levels := by
  unfold multilevelCost
  induction levels generalizing seed with
  | nil =>
      simp [multilevelCostAux]
  | cons level levels ih =>
      have hStep : 0 ≤ multilevelStepCost model family level seed :=
        multilevelStepCost_nonneg model family level seed
      have hRest : 0 ≤
          multilevelCostAux model family (fullyFixedMultilevelStep family level seed) levels :=
        ih _
      simp [multilevelCostAux]
      nlinarith

@[simp] theorem fullyFixedMultilevelRun_nil
    {cfg : FixedFormat}
    (family : FixedGridBuilderFamily cfg)
    (seed : SomeFixedGridState cfg) :
    fullyFixedMultilevelRun family seed [] = seed := by
  rfl

end FastMLFE2.FixedPrecision
