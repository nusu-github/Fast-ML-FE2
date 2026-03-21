import FastMLFE2.LocalCost

namespace FastMLFE2

namespace LocalData

variable {ι : Type*} [Fintype ι]

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
      have hsum :
          ∑ x, data.weights x * (g 0 - data.fgNeighbors x) =
            g 0 * ∑ x, data.weights x - ∑ x, data.weights x * data.fgNeighbors x := by
        calc
          ∑ x, data.weights x * (g 0 - data.fgNeighbors x)
              = ∑ x, (data.weights x * g 0 - data.weights x * data.fgNeighbors x) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  ring
          _ = (∑ x, data.weights x * g 0) - ∑ x, data.weights x * data.fgNeighbors x := by
                rw [Finset.sum_sub_distrib]
          _ = g 0 * ∑ x, data.weights x - ∑ x, data.weights x * data.fgNeighbors x := by
                rw [← Finset.sum_mul]
                ring
      rw [hsum]
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
      have hsum :
          ∑ x, data.weights x * (g 1 - data.bgNeighbors x) =
            g 1 * ∑ x, data.weights x - ∑ x, data.weights x * data.bgNeighbors x := by
        calc
          ∑ x, data.weights x * (g 1 - data.bgNeighbors x)
              = ∑ x, (data.weights x * g 1 - data.weights x * data.bgNeighbors x) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  ring
          _ = (∑ x, data.weights x * g 1) - ∑ x, data.weights x * data.bgNeighbors x := by
                rw [Finset.sum_sub_distrib]
          _ = g 1 * ∑ x, data.weights x - ∑ x, data.weights x * data.bgNeighbors x := by
                rw [← Finset.sum_mul]
                ring
      rw [hsum]
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
