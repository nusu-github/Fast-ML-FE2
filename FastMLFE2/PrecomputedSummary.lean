import FastMLFE2.SummaryForm

namespace FastMLFE2

namespace LocalData

variable {ι : Type*} [Fintype ι]

/-- Weighted foreground/background means computed from the current neighborhood state. -/
structure LocalWeightedMeans where
  fgMean : ℝ
  bgMean : ℝ

/-- Alpha-only coefficients for the normalized closed-form local update. -/
structure LocalPrecomputed where
  levelDenom : ℝ
  imageCoeffFg : ℝ
  imageCoeffBg : ℝ
  meanFgCoeffFg : ℝ
  meanBgCoeffFg : ℝ
  meanFgCoeffBg : ℝ
  meanBgCoeffBg : ℝ

def levelDenom (data : LocalData ι) (α : ℝ) : ℝ :=
  data.totalWeight + α ^ 2 + (1 - α) ^ 2

noncomputable def weightedMeans (data : LocalData ι) : LocalWeightedMeans where
  fgMean := data.foregroundSum / data.totalWeight
  bgMean := data.backgroundSum / data.totalWeight

noncomputable def precompute (data : LocalData ι) (α : ℝ) : LocalPrecomputed :=
  let s := data.totalWeight
  let b := 1 - α
  let l := data.levelDenom α
  {
    levelDenom := l
    imageCoeffFg := α / l
    imageCoeffBg := b / l
    meanFgCoeffFg := (b ^ 2 + s) / l
    meanBgCoeffFg := -(α * b) / l
    meanFgCoeffBg := -(α * b) / l
    meanBgCoeffBg := (α ^ 2 + s) / l
  }

def LocalPrecomputed.apply (coeffs : LocalPrecomputed)
    (image : ℝ) (means : LocalWeightedMeans) : FBVec :=
  mkFBVec
    (coeffs.imageCoeffFg * image
      + coeffs.meanFgCoeffFg * means.fgMean
      + coeffs.meanBgCoeffFg * means.bgMean)
    (coeffs.imageCoeffBg * image
      + coeffs.meanFgCoeffBg * means.fgMean
      + coeffs.meanBgCoeffBg * means.bgMean)

noncomputable def precomputedUpdate (data : LocalData ι) (α image : ℝ) : FBVec :=
  (data.precompute α).apply image data.weightedMeans

@[simp] theorem weightedMeans_fgMean (data : LocalData ι) :
    data.weightedMeans.fgMean = data.foregroundSum / data.totalWeight := rfl

@[simp] theorem weightedMeans_bgMean (data : LocalData ι) :
    data.weightedMeans.bgMean = data.backgroundSum / data.totalWeight := rfl

@[simp] theorem precompute_levelDenom (data : LocalData ι) (α : ℝ) :
    (data.precompute α).levelDenom = data.levelDenom α := rfl

@[simp] theorem precomputedUpdate_foreground (data : LocalData ι) (α image : ℝ) :
    foreground (data.precomputedUpdate α image) =
      (data.precompute α).imageCoeffFg * image
        + (data.precompute α).meanFgCoeffFg * data.weightedMeans.fgMean
        + (data.precompute α).meanBgCoeffFg * data.weightedMeans.bgMean := by
  simp [precomputedUpdate, LocalPrecomputed.apply]

@[simp] theorem precomputedUpdate_background (data : LocalData ι) (α image : ℝ) :
    background (data.precomputedUpdate α image) =
      (data.precompute α).imageCoeffBg * image
        + (data.precompute α).meanFgCoeffBg * data.weightedMeans.fgMean
        + (data.precompute α).meanBgCoeffBg * data.weightedMeans.bgMean := by
  simp [precomputedUpdate, LocalPrecomputed.apply]

theorem levelDenom_pos_of_totalWeight_pos (data : LocalData ι) {α : ℝ}
    (h : 0 < data.totalWeight) :
    0 < data.levelDenom α := by
  have hsquares : 0 ≤ α ^ 2 + (1 - α) ^ 2 := by positivity
  simp [levelDenom]
  nlinarith

theorem levelDenom_ne_zero_of_totalWeight_pos (data : LocalData ι) {α : ℝ}
    (h : 0 < data.totalWeight) :
    data.levelDenom α ≠ 0 :=
  (data.levelDenom_pos_of_totalWeight_pos (α := α) h).ne'

theorem weightedMeans_wellDefined (data : LocalData ι)
    (h : 0 < data.totalWeight) :
    data.totalWeight ≠ 0 := h.ne'

theorem summaryDenom_eq_totalWeight_mul_levelDenom (data : LocalData ι) (α : ℝ) :
    data.summaryDenom α = data.totalWeight * data.levelDenom α := by
  simp [LocalData.summaryDenom, levelDenom]

theorem precomputedUpdate_eq_summaryUpdate (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    data.precomputedUpdate α image = data.summaryUpdate α image := by
  apply ext_fbVec
  · have hs : data.totalWeight ≠ 0 := h.ne'
    have hl : data.levelDenom α ≠ 0 := data.levelDenom_ne_zero_of_totalWeight_pos (α := α) h
    have hd : data.summaryDenom α ≠ 0 := by
      rw [data.summaryDenom_eq_totalWeight_mul_levelDenom α]
      exact mul_ne_zero hs hl
    simp [precomputedUpdate, LocalPrecomputed.apply, precompute, weightedMeans,
      summaryUpdate, summaryForeground, levelDenom, data.summaryDenom_eq_totalWeight_mul_levelDenom]
    field_simp [hs, hl]
    ring_nf
  · have hs : data.totalWeight ≠ 0 := h.ne'
    have hl : data.levelDenom α ≠ 0 := data.levelDenom_ne_zero_of_totalWeight_pos (α := α) h
    have hd : data.summaryDenom α ≠ 0 := by
      rw [data.summaryDenom_eq_totalWeight_mul_levelDenom α]
      exact mul_ne_zero hs hl
    simp [precomputedUpdate, LocalPrecomputed.apply, precompute, weightedMeans,
      summaryUpdate, summaryBackground, levelDenom, data.summaryDenom_eq_totalWeight_mul_levelDenom]
    field_simp [hs, hl]
    ring_nf

theorem precomputedUpdate_solves_localSystem (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    data.localSystem α image (data.precomputedUpdate α image) := by
  simpa [data.precomputedUpdate_eq_summaryUpdate α image h] using
    data.summaryUpdate_solves_localSystem α image h

theorem precomputedUpdate_stationary (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    data.stationary α image (data.precomputedUpdate α image) := by
  simpa [data.precomputedUpdate_eq_summaryUpdate α image h] using
    data.summaryUpdate_stationary α image h

end LocalData

end FastMLFE2
