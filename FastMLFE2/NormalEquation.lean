import FastMLFE2.LocalCost

namespace FastMLFE2

def fbInfNorm (g : FBVec) : ℝ :=
  max (|foreground g|) (|background g|)

@[simp] theorem fbInfNorm_mkFBVec (f b : ℝ) :
    fbInfNorm (mkFBVec f b) = max |f| |b| := by
  simp [fbInfNorm]

@[simp] theorem fbInfNorm_zero : fbInfNorm 0 = 0 := by
  simp [fbInfNorm, foreground, background]

namespace LocalData

variable {ι : Type*} [Fintype ι]

private theorem sum_weight_mul_sub (w y : ι → ℝ) (x : ℝ) :
    (∑ i, w i * (x - y i)) = x * ∑ i, w i - ∑ i, w i * y i := by
  calc
    ∑ i, w i * (x - y i) = ∑ i, (w i * x - w i * y i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    _ = (∑ i, w i * x) - ∑ i, w i * y i := by
      rw [Finset.sum_sub_distrib]
    _ = x * ∑ i, w i - ∑ i, w i * y i := by
      rw [← Finset.sum_mul]
      ring

/-- The paper writes `(1 / 2) ∂cost / ∂g`; we formalize that quantity directly. -/
def halfGradient (data : LocalData ι) (α image : ℝ) (g : FBVec) : FBVec :=
  ![
    α * compositingResidual α image g +
      (∑ j, data.weights j * (foreground g - data.fgNeighbors j)),
    (1 - α) * compositingResidual α image g +
      (∑ j, data.weights j * (background g - data.bgNeighbors j))
  ]

def stationary (data : LocalData ι) (α image : ℝ) (g : FBVec) : Prop :=
  data.halfGradient α image g = 0

theorem halfGradient_foreground_eq_linearResidual (data : LocalData ι)
    (α image : ℝ) (g : FBVec) :
    foreground (data.halfGradient α image g) =
      foreground ((data.systemMatrix α).mulVec g - data.rhs α image) := by
  simp only [halfGradient, compositingResidual_eq, foreground, background, Pi.sub_apply,
    systemMatrix_mulVec_foreground]
  rw [sum_weight_mul_sub data.weights data.fgNeighbors (g 0)]
  simp [LocalData.totalWeight, LocalData.foregroundSum, rhs]
  ring

theorem halfGradient_background_eq_linearResidual (data : LocalData ι)
    (α image : ℝ) (g : FBVec) :
    background (data.halfGradient α image g) =
      background ((data.systemMatrix α).mulVec g - data.rhs α image) := by
  simp only [halfGradient, compositingResidual_eq, foreground, background, Pi.sub_apply,
    systemMatrix_mulVec_background]
  rw [sum_weight_mul_sub data.weights data.bgNeighbors (g 1)]
  simp [LocalData.totalWeight, LocalData.backgroundSum, rhs]
  ring

theorem halfGradient_eq_linearResidual (data : LocalData ι)
    (α image : ℝ) (g : FBVec) :
    data.halfGradient α image g = (data.systemMatrix α).mulVec g - data.rhs α image := by
  apply ext_fbVec
  · exact data.halfGradient_foreground_eq_linearResidual α image g
  · exact data.halfGradient_background_eq_linearResidual α image g

def localResidual (data : LocalData ι) (α image : ℝ) (g : FBVec) : FBVec :=
  data.halfGradient α image g

def localResidualInfNorm (data : LocalData ι) (α image : ℝ) (g : FBVec) : ℝ :=
  fbInfNorm (data.localResidual α image g)

def updateDeltaInfNorm (gNext gPrev : FBVec) : ℝ :=
  fbInfNorm (gNext - gPrev)

@[simp] theorem localResidual_eq_halfGradient (data : LocalData ι)
    (α image : ℝ) (g : FBVec) :
    data.localResidual α image g = data.halfGradient α image g := rfl

@[simp] theorem localResidualInfNorm_eq (data : LocalData ι)
    (α image : ℝ) (g : FBVec) :
    data.localResidualInfNorm α image g =
      max
        |foreground (data.halfGradient α image g)|
        |background (data.halfGradient α image g)| := by
  simp [localResidualInfNorm, localResidual, fbInfNorm]

@[simp] theorem updateDeltaInfNorm_eq (gNext gPrev : FBVec) :
    updateDeltaInfNorm gNext gPrev =
      max |foreground (gNext - gPrev)| |background (gNext - gPrev)| := by
  simp [updateDeltaInfNorm, fbInfNorm]

theorem stationary_iff_localSystem (data : LocalData ι) (α image : ℝ) (g : FBVec) :
    data.stationary α image g ↔ data.localSystem α image g := by
  rw [stationary, halfGradient_eq_linearResidual, localSystem]
  simpa using
    (sub_eq_zero :
      (data.systemMatrix α).mulVec g - data.rhs α image = 0 ↔
        (data.systemMatrix α).mulVec g = data.rhs α image)

theorem localResidualInfNorm_eq_zero_iff_stationary (data : LocalData ι)
    (α image : ℝ) (g : FBVec) :
    data.localResidualInfNorm α image g = 0 ↔ data.stationary α image g := by
  constructor
  · intro hzero
    rw [stationary]
    apply ext_fbVec
    · have hle :
          |foreground (data.halfGradient α image g)| ≤ 0 := by
          calc
            |foreground (data.halfGradient α image g)| ≤ data.localResidualInfNorm α image g := by
              simp [localResidualInfNorm_eq]
            _ = 0 := hzero
      have habs : |foreground (data.halfGradient α image g)| = 0 :=
        le_antisymm hle (abs_nonneg _)
      exact abs_eq_zero.mp habs
    · have hle :
          |background (data.halfGradient α image g)| ≤ 0 := by
          calc
            |background (data.halfGradient α image g)| ≤ data.localResidualInfNorm α image g := by
              simp [localResidualInfNorm_eq]
            _ = 0 := hzero
      have habs : |background (data.halfGradient α image g)| = 0 :=
        le_antisymm hle (abs_nonneg _)
      exact abs_eq_zero.mp habs
  · intro hstationary
    rw [stationary] at hstationary
    simp [localResidualInfNorm, localResidual, hstationary]

theorem updateDeltaInfNorm_eq_zero_iff (gNext gPrev : FBVec) :
    updateDeltaInfNorm gNext gPrev = 0 ↔ gNext = gPrev := by
  constructor
  · intro hzero
    apply ext_fbVec
    · have hle :
          |foreground (gNext - gPrev)| ≤ 0 := by
          calc
            |foreground (gNext - gPrev)| ≤ updateDeltaInfNorm gNext gPrev := by
              simp [updateDeltaInfNorm_eq]
            _ = 0 := hzero
      have habs : |foreground (gNext - gPrev)| = 0 := le_antisymm hle (abs_nonneg _)
      have hfg : foreground (gNext - gPrev) = 0 := abs_eq_zero.mp habs
      simpa [foreground] using (sub_eq_zero.mp hfg)
    · have hle :
          |background (gNext - gPrev)| ≤ 0 := by
          calc
            |background (gNext - gPrev)| ≤ updateDeltaInfNorm gNext gPrev := by
              simp [updateDeltaInfNorm_eq]
            _ = 0 := hzero
      have habs : |background (gNext - gPrev)| = 0 := le_antisymm hle (abs_nonneg _)
      have hbg : background (gNext - gPrev) = 0 := abs_eq_zero.mp habs
      simpa [background] using (sub_eq_zero.mp hbg)
  · intro hEq
    simp [updateDeltaInfNorm, hEq]

end LocalData

end FastMLFE2
