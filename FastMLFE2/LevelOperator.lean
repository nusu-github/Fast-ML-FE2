import FastMLFE2.SummaryForm

namespace FastMLFE2

namespace LocalData

variable {ι : Type*} [Fintype ι]

/-- Weighted foreground/background means computed from the current neighborhood state. -/
structure LocalWeightedMeans where
  fgMean : ℝ
  bgMean : ℝ

/-- Level-fixed operator for the mean + residual correction form of the local update. -/
structure LevelOperator where
  alpha : ℝ
  beta : ℝ
  invLevelDenom : ℝ

def levelDenom (data : LocalData ι) (α : ℝ) : ℝ :=
  data.totalWeight + α ^ 2 + (1 - α) ^ 2

noncomputable def weightedMeans (data : LocalData ι) : LocalWeightedMeans where
  fgMean := data.foregroundSum / data.totalWeight
  bgMean := data.backgroundSum / data.totalWeight

noncomputable def buildLevelOperator (data : LocalData ι) (α : ℝ) : LevelOperator where
  alpha := α
  beta := 1 - α
  invLevelDenom := 1 / data.levelDenom α

def LevelOperator.meanResidual (op : LevelOperator)
    (image : ℝ) (means : LocalWeightedMeans) : ℝ :=
  image - op.alpha * means.fgMean - op.beta * means.bgMean

noncomputable def LevelOperator.apply (op : LevelOperator)
    (image : ℝ) (means : LocalWeightedMeans) : FBVec :=
  let residual := op.meanResidual image means
  mkFBVec
    (means.fgMean + op.alpha * op.invLevelDenom * residual)
    (means.bgMean + op.beta * op.invLevelDenom * residual)

/-- Canonical local update: normalized means plus compositing-residual correction. -/
noncomputable def levelOperatorUpdate (data : LocalData ι) (α image : ℝ) : FBVec :=
  (data.buildLevelOperator α).apply image data.weightedMeans

@[simp] theorem weightedMeans_fgMean (data : LocalData ι) :
    data.weightedMeans.fgMean = data.foregroundSum / data.totalWeight := rfl

@[simp] theorem weightedMeans_bgMean (data : LocalData ι) :
    data.weightedMeans.bgMean = data.backgroundSum / data.totalWeight := rfl

@[simp] theorem buildLevelOperator_alpha (data : LocalData ι) (α : ℝ) :
    (data.buildLevelOperator α).alpha = α := rfl

@[simp] theorem buildLevelOperator_beta (data : LocalData ι) (α : ℝ) :
    (data.buildLevelOperator α).beta = 1 - α := rfl

@[simp] theorem buildLevelOperator_invLevelDenom (data : LocalData ι) (α : ℝ) :
    (data.buildLevelOperator α).invLevelDenom = 1 / data.levelDenom α := rfl

theorem buildLevelOperator_eq_of_totalWeight_eq
    {data₁ data₂ : LocalData ι} (h : data₁.totalWeight = data₂.totalWeight) (α : ℝ) :
    data₁.buildLevelOperator α = data₂.buildLevelOperator α := by
  change
    LevelOperator.mk α (1 - α) (1 / data₁.levelDenom α) =
      LevelOperator.mk α (1 - α) (1 / data₂.levelDenom α)
  simp [levelDenom, h]

@[simp] theorem meanResidual_eq (op : LevelOperator)
    (image : ℝ) (means : LocalWeightedMeans) :
    op.meanResidual image means = image - op.alpha * means.fgMean - op.beta * means.bgMean := rfl

@[simp] theorem levelOperatorUpdate_foreground (data : LocalData ι) (α image : ℝ) :
    foreground (data.levelOperatorUpdate α image) =
      data.weightedMeans.fgMean
        + (data.buildLevelOperator α).alpha
            * (data.buildLevelOperator α).invLevelDenom
            * (data.buildLevelOperator α).meanResidual image data.weightedMeans := by
  simp [levelOperatorUpdate, LevelOperator.apply]

@[simp] theorem levelOperatorUpdate_background (data : LocalData ι) (α image : ℝ) :
    background (data.levelOperatorUpdate α image) =
      data.weightedMeans.bgMean
        + (data.buildLevelOperator α).beta
            * (data.buildLevelOperator α).invLevelDenom
            * (data.buildLevelOperator α).meanResidual image data.weightedMeans := by
  simp [levelOperatorUpdate, LevelOperator.apply]

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

theorem levelOperatorUpdate_foreground_eq_summary (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    foreground (data.levelOperatorUpdate α image) = data.summaryForeground α image := by
  have hs : data.totalWeight ≠ 0 := data.weightedMeans_wellDefined h
  have hl : data.levelDenom α ≠ 0 := data.levelDenom_ne_zero_of_totalWeight_pos (α := α) h
  simp [levelOperatorUpdate, LevelOperator.apply, LevelOperator.meanResidual,
    weightedMeans, buildLevelOperator, summaryForeground, levelDenom,
    data.summaryDenom_eq_totalWeight_mul_levelDenom]
  field_simp [hs, hl]
  ring_nf

theorem levelOperatorUpdate_background_eq_summary (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    background (data.levelOperatorUpdate α image) = data.summaryBackground α image := by
  have hs : data.totalWeight ≠ 0 := data.weightedMeans_wellDefined h
  have hl : data.levelDenom α ≠ 0 := data.levelDenom_ne_zero_of_totalWeight_pos (α := α) h
  simp [levelOperatorUpdate, LevelOperator.apply, LevelOperator.meanResidual,
    weightedMeans, buildLevelOperator, summaryBackground, levelDenom,
    data.summaryDenom_eq_totalWeight_mul_levelDenom]
  field_simp [hs, hl]
  ring_nf

theorem levelOperatorUpdate_eq_summaryUpdate (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    data.levelOperatorUpdate α image = data.summaryUpdate α image := by
  apply ext_fbVec
  · simpa [summaryUpdate] using data.levelOperatorUpdate_foreground_eq_summary α image h
  · simpa [summaryUpdate] using data.levelOperatorUpdate_background_eq_summary α image h

theorem levelOperatorUpdate_solves_localSystem (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    data.localSystem α image (data.levelOperatorUpdate α image) := by
  simpa [data.levelOperatorUpdate_eq_summaryUpdate α image h] using
    data.summaryUpdate_solves_localSystem α image h

theorem levelOperatorUpdate_stationary (data : LocalData ι)
    (α image : ℝ) (h : 0 < data.totalWeight) :
    data.stationary α image (data.levelOperatorUpdate α image) := by
  simpa [data.levelOperatorUpdate_eq_summaryUpdate α image h] using
    data.summaryUpdate_stationary α image h

end LocalData

end FastMLFE2
