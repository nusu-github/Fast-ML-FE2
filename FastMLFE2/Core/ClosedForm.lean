import FastMLFE2.Core.LocalEquation

namespace FastMLFE2.Core

/-!
Closed-form solution definitions for the 2×2 local normal equation.

These definitions are separated from the correctness theorems (in `Theorems.ClosedForm`)
so that lower layers (`Level.Jacobi`) can reference the solution without importing the
theorem layer.
-/

namespace LocalContext

variable {ι : Type*} [Fintype ι]

def closedFormDenom (ctx : LocalContext ι) : ℝ :=
  ctx.totalWeight * ctx.weightedMeanDenom

def closedFormForegroundNumerator (ctx : LocalContext ι) : ℝ :=
  ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) * foreground ctx.rhs -
    ctx.alphaCenter * (1 - ctx.alphaCenter) * background ctx.rhs

def closedFormBackgroundNumerator (ctx : LocalContext ι) : ℝ :=
  (ctx.alphaCenter ^ 2 + ctx.totalWeight) * background ctx.rhs -
    ctx.alphaCenter * (1 - ctx.alphaCenter) * foreground ctx.rhs

noncomputable def closedFormSolution (ctx : LocalContext ι) : LocalUnknown :=
  let b := ctx.rhs
  let det := closedFormDenom ctx
  ![
    (((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight) * foreground b -
      ctx.alphaCenter * (1 - ctx.alphaCenter) * background b) / det,
    ((ctx.alphaCenter ^ 2 + ctx.totalWeight) * background b -
      ctx.alphaCenter * (1 - ctx.alphaCenter) * foreground b) / det
  ]

noncomputable def inverseSolution (ctx : LocalContext ι) : LocalUnknown :=
  (ctx.normalMatrix⁻¹).mulVec ctx.rhs

@[simp] theorem foreground_closedFormSolution (ctx : LocalContext ι) :
    foreground (closedFormSolution ctx) =
      closedFormForegroundNumerator ctx / closedFormDenom ctx := by
  simp [closedFormSolution, closedFormForegroundNumerator, foreground, background]

@[simp] theorem background_closedFormSolution (ctx : LocalContext ι) :
    background (closedFormSolution ctx) =
      closedFormBackgroundNumerator ctx / closedFormDenom ctx := by
  simp [closedFormSolution, closedFormBackgroundNumerator, foreground, background]

end LocalContext

end FastMLFE2.Core
