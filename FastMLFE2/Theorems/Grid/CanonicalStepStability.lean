import FastMLFE2.Theorems.Grid.CanonicalMultilevelConvergence
import FastMLFE2.Canonical.GridContext
import FastMLFE2.Theorems.Grid.GridAssumptions
import FastMLFE2.Theorems.Grid.GridNonempty
import FastMLFE2.Theorems.Grid.IterationInvariance
import FastMLFE2.Theorems.Grid.ChannelReuse
import FastMLFE2.Theorems.Approximation.NearBinary
import FastMLFE2.Theorems.Solvability.Invertibility

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions
open FastMLFE2.Level
open FastMLFE2.Canonical
open FastMLFE2.Core.LocalContext

namespace LocalContext

variable {ι : Type*} [Fintype ι]

noncomputable def closedFormForegroundLipschitzFactor (ctx : LocalContext ι) : ℝ :=
  (jacobiDiagBackground ctx + jacobiCrossTerm ctx) / closedFormDenom ctx

noncomputable def closedFormBackgroundLipschitzFactor (ctx : LocalContext ι) : ℝ :=
  (jacobiDiagForeground ctx + jacobiCrossTerm ctx) / closedFormDenom ctx

noncomputable def closedFormOneStepGain (ctx : LocalContext ι) : ℝ :=
  ctx.totalWeight *
    max (closedFormForegroundLipschitzFactor ctx) (closedFormBackgroundLipschitzFactor ctx)

theorem closedFormForegroundLipschitzFactor_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ closedFormForegroundLipschitzFactor ctx := by
  unfold closedFormForegroundLipschitzFactor
  exact div_nonneg
    (add_nonneg (jacobiDiagBackground_pos ctx).le (jacobiCrossTerm_nonneg ctx))
    (closedFormDenom_pos ctx).le

theorem closedFormBackgroundLipschitzFactor_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ closedFormBackgroundLipschitzFactor ctx := by
  unfold closedFormBackgroundLipschitzFactor
  exact div_nonneg
    (add_nonneg (jacobiDiagForeground_pos ctx).le (jacobiCrossTerm_nonneg ctx))
    (closedFormDenom_pos ctx).le

theorem closedFormOneStepGain_nonneg
    (ctx : LocalContext ι) [CoreMathAssumptions ctx] :
    0 ≤ closedFormOneStepGain ctx := by
  unfold closedFormOneStepGain
  exact mul_nonneg (le_of_lt (totalWeight_pos ctx))
    (le_trans
      (closedFormForegroundLipschitzFactor_nonneg ctx)
      (le_max_left _ _))

end LocalContext

namespace Canonical

open scoped Classical

noncomputable def gridStateDistance
    (spec : RealLevelSpec)
    (x y : GridState spec.height spec.width) : ℝ :=
  gridStateInfinityNorm spec (fun p => x p - y p)

theorem gridStateDistance_nonneg
    (spec : RealLevelSpec)
    (x y : GridState spec.height spec.width) :
    0 ≤ gridStateDistance spec x y :=
  gridStateInfinityNorm_nonneg spec (fun p => x p - y p)

theorem localInfinityNorm_sub_le_gridStateDistance
    (spec : RealLevelSpec)
    (x y : GridState spec.height spec.width)
    (p : Pixel spec.height spec.width) :
    LocalContext.localInfinityNorm (x p - y p) ≤ gridStateDistance spec x y :=
  localInfinityNorm_le_gridStateInfinityNorm spec (fun p => x p - y p) p

theorem gridStateDistance_le_of_pointwise
    (spec : RealLevelSpec)
    (x y : GridState spec.height spec.width)
    {C : ℝ}
    (hC : ∀ p, LocalContext.localInfinityNorm (x p - y p) ≤ C) :
    gridStateDistance spec x y ≤ C := by
  unfold gridStateDistance gridStateInfinityNorm
  letI : Nonempty (Pixel spec.height spec.width) := ⟨basePixel spec⟩
  by_contra hdist
  have hlt :
      C <
        (Finset.univ.image fun p : Pixel spec.height spec.width =>
          LocalContext.localInfinityNorm (x p - y p)).max'
          (Finset.image_nonempty.mpr Finset.univ_nonempty) :=
    lt_of_not_ge hdist
  have hmem :
      (Finset.univ.image fun p : Pixel spec.height spec.width =>
        LocalContext.localInfinityNorm (x p - y p)).max'
        (Finset.image_nonempty.mpr Finset.univ_nonempty) ∈
      Finset.univ.image fun p : Pixel spec.height spec.width =>
        LocalContext.localInfinityNorm (x p - y p) :=
    Finset.max'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨p, _, hp⟩
  exact not_le_of_gt hlt (hp ▸ hC p)

@[simp] theorem gridStateDistance_self
    (spec : RealLevelSpec)
    (x : GridState spec.height spec.width) :
    gridStateDistance spec x x = 0 := by
  apply le_antisymm
  · refine gridStateDistance_le_of_pointwise spec x x ?_
    intro p
    simp [FastMLFE2.Core.LocalContext.localInfinityNorm, foreground, background]
  · exact gridStateDistance_nonneg spec x x

theorem localInfinityNorm_add_le
    (g h : LocalUnknown) :
    LocalContext.localInfinityNorm (g + h) ≤
      LocalContext.localInfinityNorm g + LocalContext.localInfinityNorm h := by
  unfold FastMLFE2.Core.LocalContext.localInfinityNorm
  refine max_le ?_ ?_
  · have hleft :
        |foreground (g + h)| ≤ |foreground g| + |foreground h| := by
          have hsum : foreground (g + h) = foreground g + foreground h := by
            simp [foreground]
          rw [hsum]
          refine abs_le.mpr ?_
          constructor <;> nlinarith [neg_abs_le (foreground g), neg_abs_le (foreground h),
            le_abs_self (foreground g), le_abs_self (foreground h)]
    exact hleft.trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · have hright :
        |background (g + h)| ≤ |background g| + |background h| := by
          have hsum : background (g + h) = background g + background h := by
            simp [background]
          rw [hsum]
          refine abs_le.mpr ?_
          constructor <;> nlinarith [neg_abs_le (background g), neg_abs_le (background h),
            le_abs_self (background g), le_abs_self (background h)]
    exact hright.trans (add_le_add (le_max_right _ _) (le_max_right _ _))

theorem localInfinityNorm_triangle
    (x y z : LocalUnknown) :
    LocalContext.localInfinityNorm (x - z) ≤
      LocalContext.localInfinityNorm (x - y) + LocalContext.localInfinityNorm (y - z) := by
  have hadd : x - z = (x - y) + (y - z) := by
    ext i
    fin_cases i <;> simp [sub_eq_add_neg] <;> ring
  rw [hadd]
  exact localInfinityNorm_add_le _ _

theorem gridStateDistance_triangle
    (spec : RealLevelSpec)
    (x y z : GridState spec.height spec.width) :
    gridStateDistance spec x z ≤
      gridStateDistance spec x y + gridStateDistance spec y z := by
  refine gridStateDistance_le_of_pointwise spec x z ?_
  intro p
  calc
    LocalContext.localInfinityNorm (x p - z p)
      ≤ LocalContext.localInfinityNorm (x p - y p) +
          LocalContext.localInfinityNorm (y p - z p) :=
        localInfinityNorm_triangle (x p) (y p) (z p)
    _ ≤ gridStateDistance spec x y + gridStateDistance spec y z := by
      exact add_le_add
        (localInfinityNorm_sub_le_gridStateDistance spec x y p)
        (localInfinityNorm_sub_le_gridStateDistance spec y z p)

def LocalUnknownBoxed (g : LocalUnknown) : Prop :=
  0 ≤ foreground g ∧ foreground g ≤ 1 ∧ 0 ≤ background g ∧ background g ≤ 1

def GridStateBoxed
    (spec : RealLevelSpec)
    (state : GridState spec.height spec.width) : Prop :=
  ∀ p, LocalUnknownBoxed (state p)

noncomputable def binaryZeroProxyLocal {ι : Type*} [Fintype ι] (ctx : Core.LocalContext ι) :
    LocalUnknown :=
  ![ctx.foregroundMean,
    ctx.backgroundMean + (ctx.imageValue - ctx.backgroundMean) / (ctx.totalWeight + 1)]

noncomputable def binaryOneProxyLocal {ι : Type*} [Fintype ι] (ctx : Core.LocalContext ι) :
    LocalUnknown :=
  ![ctx.foregroundMean + (ctx.imageValue - ctx.foregroundMean) / (ctx.totalWeight + 1),
    ctx.backgroundMean]

private theorem correctedMean_mem_Icc
    {μ I W : ℝ}
    (hW : 0 ≤ W)
    (hμ : 0 ≤ μ ∧ μ ≤ 1)
    (hI : 0 ≤ I ∧ I ≤ 1) :
    0 ≤ μ + (I - μ) / (W + 1) ∧ μ + (I - μ) / (W + 1) ≤ 1 := by
  have hD : 0 < W + 1 := by linarith
  have hD0 : W + 1 ≠ 0 := hD.ne'
  have hEq : μ + (I - μ) / (W + 1) = (W * μ + I) / (W + 1) := by
    field_simp [hD0]
    ring
  constructor
  · rw [hEq]
    refine div_nonneg ?_ hD.le
    nlinarith [hW, hμ.1, hI.1]
  · rw [hEq]
    have hnum : W * μ + I ≤ W + 1 := by
      nlinarith [hW, hμ.2, hI.2]
    rw [div_le_iff₀ hD]
    simpa using hnum

theorem binaryZeroProxyLocal_boxed
    {ι : Type*} [Fintype ι]
    (ctx : Core.LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    LocalUnknownBoxed (binaryZeroProxyLocal ctx) := by
  have hμF := FastMLFE2.Theorems.LocalContext.foregroundMean_mem_Icc_of_boxedNeighbors ctx hfg
  have hμB := FastMLFE2.Theorems.LocalContext.backgroundMean_mem_Icc_of_boxedNeighbors ctx hbg
  have hcorr := correctedMean_mem_Icc
    (le_of_lt (FastMLFE2.Theorems.LocalContext.totalWeight_pos ctx)) hμB hI
  exact ⟨by simpa [LocalUnknownBoxed, binaryZeroProxyLocal, foreground, background] using hμF.1,
    ⟨by simpa [LocalUnknownBoxed, binaryZeroProxyLocal, foreground, background] using hμF.2,
      ⟨by simpa [LocalUnknownBoxed, binaryZeroProxyLocal, foreground, background] using hcorr.1,
        by simpa [LocalUnknownBoxed, binaryZeroProxyLocal, foreground, background] using hcorr.2⟩⟩⟩

theorem binaryOneProxyLocal_boxed
    {ι : Type*} [Fintype ι]
    (ctx : Core.LocalContext ι) [CoreMathAssumptions ctx]
    (hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1)
    (hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1)
    (hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1) :
    LocalUnknownBoxed (binaryOneProxyLocal ctx) := by
  have hμF := FastMLFE2.Theorems.LocalContext.foregroundMean_mem_Icc_of_boxedNeighbors ctx hfg
  have hμB := FastMLFE2.Theorems.LocalContext.backgroundMean_mem_Icc_of_boxedNeighbors ctx hbg
  have hcorr := correctedMean_mem_Icc
    (le_of_lt (FastMLFE2.Theorems.LocalContext.totalWeight_pos ctx)) hμF hI
  exact ⟨by simpa [LocalUnknownBoxed, binaryOneProxyLocal, foreground, background] using hcorr.1,
    ⟨by simpa [LocalUnknownBoxed, binaryOneProxyLocal, foreground, background] using hcorr.2,
      ⟨by simpa [LocalUnknownBoxed, binaryOneProxyLocal, foreground, background] using hμB.1,
        by simpa [LocalUnknownBoxed, binaryOneProxyLocal, foreground, background] using hμB.2⟩⟩⟩

noncomputable def nearBinaryProxyAt
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    (τ : ℝ)
    (state : GridState spec.height spec.width)
    (p : Pixel spec.height spec.width) : LocalUnknown := by
  let ctx := (data spec.height spec.width).localCtx p state
  by_cases hboxed : GridStateBoxed spec state
  · by_cases hα0 : (data spec.height spec.width).alpha p ≤ τ
    · exact binaryZeroProxyLocal ctx
    · by_cases hα1 : 1 - (data spec.height spec.width).alpha p ≤ τ
      · exact binaryOneProxyLocal ctx
      · exact LocalContext.closedFormSolution ctx
  · exact LocalContext.closedFormSolution ctx

noncomputable def nearBinaryProxyStep
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    (τ : ℝ)
    (state : GridState spec.height spec.width) : GridState spec.height spec.width :=
  fun p => nearBinaryProxyAt data spec τ state p

@[simp] theorem nearBinaryProxyAt_eq_closedForm_of_not_boxed
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    (τ : ℝ)
    (state : GridState spec.height spec.width)
    (p : Pixel spec.height spec.width)
    (hboxed : ¬ GridStateBoxed spec state) :
    nearBinaryProxyAt data spec τ state p =
      LocalContext.closedFormSolution ((data spec.height spec.width).localCtx p state) := by
  classical
  simp [nearBinaryProxyAt, hboxed]

@[simp] theorem nearBinaryProxyStep_eq_exact_of_not_boxed
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    (τ : ℝ)
    (state : GridState spec.height spec.width)
    (hboxed : ¬ GridStateBoxed spec state) :
    nearBinaryProxyStep data spec τ state =
      (data spec.height spec.width).toCanonicalPixelData.canonicalBuilder.jacobiStep state := by
  funext p
  simp [nearBinaryProxyStep, nearBinaryProxyAt, hboxed]

theorem nearBinaryProxyAt_boxed
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    [Fact (2 ≤ spec.height)] [Fact (2 ≤ spec.width)]
    [GridMathAssumptions (data spec.height spec.width)]
    (τ : ℝ)
    (state : GridState spec.height spec.width)
    (himage : ∀ p, 0 ≤ (data spec.height spec.width).image p ∧
      (data spec.height spec.width).image p ≤ 1)
    (hboxed : GridStateBoxed spec state)
    (hnear : ∀ p,
      (data spec.height spec.width).alpha p ≤ τ ∨
        1 - (data spec.height spec.width).alpha p ≤ τ)
    (p : Pixel spec.height spec.width) :
    LocalUnknownBoxed (nearBinaryProxyAt data spec τ state p) := by
  classical
  let ctx : Core.LocalContext (ValidDir p) := (data spec.height spec.width).localCtx p state
  letI : Fact (Nonempty (ValidDir p)) :=
    ⟨_root_.FastMLFE2.Theorems.nonempty_validDir_of_height_two_le p⟩
  haveI : CoreMathAssumptions ctx := by
    simpa [ctx] using
      (_root_.FastMLFE2.Theorems.GridPixelData.coreMathAssumptions_of_gridMathAssumptions
        (data := data spec.height spec.width) (state := state) (p := p))
  have hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1 := by
    simpa [ctx, GridPixelData.localCtx] using himage p
  have hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1 := by
    intro j
    exact ⟨(hboxed ((data spec.height spec.width).toCanonicalPixelData.neighborPixel p j)).1,
      (hboxed ((data spec.height spec.width).toCanonicalPixelData.neighborPixel p j)).2.1⟩
  have hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1 := by
    intro j
    exact ⟨(hboxed ((data spec.height spec.width).toCanonicalPixelData.neighborPixel p j)).2.2.1,
      (hboxed ((data spec.height spec.width).toCanonicalPixelData.neighborPixel p j)).2.2.2⟩
  by_cases hα0 : (data spec.height spec.width).alpha p ≤ τ
  · have hproxy :
        nearBinaryProxyAt data spec τ state p = binaryZeroProxyLocal ctx := by
          simp [nearBinaryProxyAt, ctx, hboxed, hα0]
    rw [hproxy]
    exact binaryZeroProxyLocal_boxed ctx hI hfg hbg
  · have hα1 : 1 - (data spec.height spec.width).alpha p ≤ τ := by
      rcases hnear p with hα | hα
      · exact (hα0 hα).elim
      · exact hα
    have hproxy :
        nearBinaryProxyAt data spec τ state p = binaryOneProxyLocal ctx := by
          simp [nearBinaryProxyAt, ctx, hboxed, hα0, hα1]
    rw [hproxy]
    exact binaryOneProxyLocal_boxed ctx hI hfg hbg

theorem nearBinaryProxyStep_boxed
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    [Fact (2 ≤ spec.height)] [Fact (2 ≤ spec.width)]
    [GridMathAssumptions (data spec.height spec.width)]
    (τ : ℝ)
    (state : GridState spec.height spec.width)
    (himage : ∀ p, 0 ≤ (data spec.height spec.width).image p ∧
      (data spec.height spec.width).image p ≤ 1)
    (hboxed : GridStateBoxed spec state)
    (hnear : ∀ p,
      (data spec.height spec.width).alpha p ≤ τ ∨
        1 - (data spec.height spec.width).alpha p ≤ τ) :
    GridStateBoxed spec (nearBinaryProxyStep data spec τ state) := by
  intro p
  simpa [nearBinaryProxyStep] using nearBinaryProxyAt_boxed data spec τ state himage hboxed hnear p

theorem canonical_jacobiUpdateAt_proxy_gap_le
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    [Fact (2 ≤ spec.height)] [Fact (2 ≤ spec.width)]
    [GridMathAssumptions (data spec.height spec.width)]
    (τ : ℝ)
    (state : GridState spec.height spec.width)
    (himage : ∀ p, 0 ≤ (data spec.height spec.width).image p ∧
      (data spec.height spec.width).image p ≤ 1)
    (hboxed : GridStateBoxed spec state)
    (hnear : ∀ p,
      (data spec.height spec.width).alpha p ≤ τ ∨
        1 - (data spec.height spec.width).alpha p ≤ τ)
    (p : Pixel spec.height spec.width) :
    LocalContext.localInfinityNorm
        (((data spec.height spec.width).toCanonicalPixelData.canonicalBuilder.jacobiStep state) p -
          nearBinaryProxyAt data spec τ state p) ≤
      4 * τ := by
  classical
  let ctx : Core.LocalContext (ValidDir p) := (data spec.height spec.width).localCtx p state
  letI : Fact (Nonempty (ValidDir p)) :=
    ⟨_root_.FastMLFE2.Theorems.nonempty_validDir_of_height_two_le p⟩
  haveI : CoreMathAssumptions ctx := by
    simpa [ctx] using
      (_root_.FastMLFE2.Theorems.GridPixelData.coreMathAssumptions_of_gridMathAssumptions
        (data := data spec.height spec.width) (state := state) (p := p))
  have hI : 0 ≤ ctx.imageValue ∧ ctx.imageValue ≤ 1 := by
    simpa [ctx, GridPixelData.localCtx] using himage p
  have hfg : ∀ j, 0 ≤ ctx.fgNeighbor j ∧ ctx.fgNeighbor j ≤ 1 := by
    intro j
    exact ⟨(hboxed ((data spec.height spec.width).toCanonicalPixelData.neighborPixel p j)).1,
      (hboxed ((data spec.height spec.width).toCanonicalPixelData.neighborPixel p j)).2.1⟩
  have hbg : ∀ j, 0 ≤ ctx.bgNeighbor j ∧ ctx.bgNeighbor j ≤ 1 := by
    intro j
    exact ⟨(hboxed ((data spec.height spec.width).toCanonicalPixelData.neighborPixel p j)).2.2.1,
      (hboxed ((data spec.height spec.width).toCanonicalPixelData.neighborPixel p j)).2.2.2⟩
  by_cases hα0 : (data spec.height spec.width).alpha p ≤ τ
  · have hproxy :
        nearBinaryProxyAt data spec τ state p = binaryZeroProxyLocal ctx := by
          simp [nearBinaryProxyAt, ctx, hboxed, hα0]
    rw [hproxy]
    have hα0ctx : ctx.alphaCenter ≤ τ := by
      simpa [ctx, GridPixelData.localCtx] using hα0
    simpa [ctx, GridPixelData.localCtx] using
      FastMLFE2.Theorems.LocalContext.localInfinityNorm_sub_binaryZeroCtx_le_of_alpha_le_tau
        (ctx := ctx) hI hfg hbg hα0ctx
  · have hα1 : 1 - (data spec.height spec.width).alpha p ≤ τ := by
      rcases hnear p with hα | hα
      · exact (hα0 hα).elim
      · exact hα
    have hproxy :
        nearBinaryProxyAt data spec τ state p = binaryOneProxyLocal ctx := by
          simp [nearBinaryProxyAt, ctx, hboxed, hα0, hα1]
    rw [hproxy]
    have hα1ctx : 1 - ctx.alphaCenter ≤ τ := by
      simpa [ctx, GridPixelData.localCtx] using hα1
    simpa [ctx, GridPixelData.localCtx] using
      FastMLFE2.Theorems.LocalContext.localInfinityNorm_sub_binaryOneCtx_le_of_one_minus_alpha_le_tau
        (ctx := ctx) hI hfg hbg hα1ctx

theorem canonical_jacobiStep_proxy_gap_le
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    [Fact (2 ≤ spec.height)] [Fact (2 ≤ spec.width)]
    [GridMathAssumptions (data spec.height spec.width)]
    (τ : ℝ)
    (state : GridState spec.height spec.width)
    (himage : ∀ p, 0 ≤ (data spec.height spec.width).image p ∧
      (data spec.height spec.width).image p ≤ 1)
    (hboxed : GridStateBoxed spec state)
    (hnear : ∀ p,
      (data spec.height spec.width).alpha p ≤ τ ∨
        1 - (data spec.height spec.width).alpha p ≤ τ) :
    gridStateDistance spec
        ((data spec.height spec.width).toCanonicalPixelData.canonicalBuilder.jacobiStep state)
        (nearBinaryProxyStep data spec τ state) ≤
      4 * τ := by
  refine gridStateDistance_le_of_pointwise spec _ _ ?_
  intro p
  simpa [gridStateDistance, nearBinaryProxyStep] using
    canonical_jacobiUpdateAt_proxy_gap_le data spec τ state himage hboxed hnear p

theorem canonical_jacobiStep_proxy_gap_le_unconditional
    (data : (h w : Nat) → GridPixelData h w)
    (spec : RealLevelSpec)
    [Fact (2 ≤ spec.height)] [Fact (2 ≤ spec.width)]
    [GridMathAssumptions (data spec.height spec.width)]
    (τ : ℝ)
    (hτ : 0 ≤ τ)
    (state : GridState spec.height spec.width)
    (himage : ∀ p, 0 ≤ (data spec.height spec.width).image p ∧
      (data spec.height spec.width).image p ≤ 1)
    (hnear : ∀ p,
      (data spec.height spec.width).alpha p ≤ τ ∨
        1 - (data spec.height spec.width).alpha p ≤ τ) :
    gridStateDistance spec
        ((data spec.height spec.width).toCanonicalPixelData.canonicalBuilder.jacobiStep state)
        (nearBinaryProxyStep data spec τ state) ≤
      4 * τ := by
  by_cases hboxed : GridStateBoxed spec state
  · exact canonical_jacobiStep_proxy_gap_le data spec τ state himage hboxed hnear
  · rw [nearBinaryProxyStep_eq_exact_of_not_boxed data spec τ state hboxed]
    have hzero : gridStateDistance spec
        ((data spec.height spec.width).toCanonicalPixelData.canonicalBuilder.jacobiStep state)
        ((data spec.height spec.width).toCanonicalPixelData.canonicalBuilder.jacobiStep state) = 0 :=
      gridStateDistance_self spec _
    rw [hzero]
    nlinarith

end Canonical

end FastMLFE2.Theorems
