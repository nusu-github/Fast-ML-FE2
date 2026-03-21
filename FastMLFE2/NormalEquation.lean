import FastMLFE2.LocalCost

namespace FastMLFE2

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

theorem halfGradient_eq_linearResidual (data : LocalData ι)
    (α image : ℝ) (g : FBVec) :
    data.halfGradient α image g = (data.systemMatrix α).mulVec g - data.rhs α image := by
  ext i
  fin_cases i
  · have hcomp :
        α * compositingResidual α image g
            + ∑ j, data.weights j * (foreground g - data.fgNeighbors j) =
          (data.systemMatrix α).mulVec g 0 - data.rhs α image 0 := by
      rw [systemMatrix_mulVec_foreground]
      have hrhs : data.rhs α image 0 = α * image + data.foregroundSum := by
        simp [rhs]
      rw [hrhs]
      simp only [compositingResidual_eq, foreground, background]
      rw [sum_weight_mul_sub data.weights data.fgNeighbors (g 0)]
      rw [LocalData.totalWeight, LocalData.foregroundSum]
      ring
    simpa [halfGradient, Pi.sub_apply] using hcomp
  · have hcomp :
        (1 - α) * compositingResidual α image g
            + ∑ j, data.weights j * (background g - data.bgNeighbors j) =
          (data.systemMatrix α).mulVec g 1 - data.rhs α image 1 := by
      rw [systemMatrix_mulVec_background]
      have hrhs : data.rhs α image 1 = (1 - α) * image + data.backgroundSum := by
        simp [rhs]
      rw [hrhs]
      simp only [compositingResidual_eq, foreground, background]
      rw [sum_weight_mul_sub data.weights data.bgNeighbors (g 1)]
      rw [LocalData.totalWeight, LocalData.backgroundSum]
      ring
    simpa [halfGradient, Pi.sub_apply] using hcomp

theorem stationary_iff_localSystem (data : LocalData ι) (α image : ℝ) (g : FBVec) :
    data.stationary α image g ↔ data.localSystem α image g := by
  rw [stationary, halfGradient_eq_linearResidual, localSystem]
  simpa using
    (sub_eq_zero :
      (data.systemMatrix α).mulVec g - data.rhs α image = 0 ↔
        (data.systemMatrix α).mulVec g = data.rhs α image)

end LocalData

end FastMLFE2
