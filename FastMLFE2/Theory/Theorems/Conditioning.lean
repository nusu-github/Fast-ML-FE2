import FastMLFE2.Theory.Theorems.Invertibility

namespace FastMLFE2.Theory.Theorems

/-!
H12 local conditioning structure for the single-pixel normal matrix.
-/

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

private def alphaQuadratic (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter ^ 2 + (1 - ctx.alphaCenter) ^ 2

private def orthVec (ctx : LocalContext ι) : LocalUnknown :=
  ![1 - ctx.alphaCenter, -ctx.alphaCenter]

theorem normalMatrix_eq_totalWeight_plus_uOuter
    (ctx : LocalContext ι) :
    ctx.normalMatrix =
      ![![ctx.totalWeight + ctx.alphaCenter ^ 2,
          ctx.alphaCenter * (1 - ctx.alphaCenter)],
        ![ctx.alphaCenter * (1 - ctx.alphaCenter),
          ctx.totalWeight + (1 - ctx.alphaCenter) ^ 2]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LocalContext.normalMatrix, add_comm]

end LocalContext

end FastMLFE2.Theory.Theorems
