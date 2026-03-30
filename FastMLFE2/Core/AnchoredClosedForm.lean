import FastMLFE2.Core.AnchoredLocalEquation

namespace FastMLFE2.Core

/-!
Closed-form solution for the anchored local normal equation.
-/

namespace AnchoredLocalContext

variable {ι : Type*} [Fintype ι]

def closedFormDenom (ctx : AnchoredLocalContext ι) : ℝ :=
  ((ctx.alphaCenter ^ 2 + ctx.totalWeight + ctx.fgAnchorWeight) *
      ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight + ctx.bgAnchorWeight)) -
    (ctx.alphaCenter * (1 - ctx.alphaCenter)) ^ 2

def closedFormForegroundNumerator (ctx : AnchoredLocalContext ι) : ℝ :=
  ((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight + ctx.bgAnchorWeight) * foreground ctx.rhs -
    ctx.alphaCenter * (1 - ctx.alphaCenter) * background ctx.rhs

def closedFormBackgroundNumerator (ctx : AnchoredLocalContext ι) : ℝ :=
  (ctx.alphaCenter ^ 2 + ctx.totalWeight + ctx.fgAnchorWeight) * background ctx.rhs -
    ctx.alphaCenter * (1 - ctx.alphaCenter) * foreground ctx.rhs

noncomputable def closedFormSolution (ctx : AnchoredLocalContext ι) : LocalUnknown :=
  let b := ctx.rhs
  let det := closedFormDenom ctx
  ![
    (((1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight + ctx.bgAnchorWeight) * foreground b -
      ctx.alphaCenter * (1 - ctx.alphaCenter) * background b) / det,
    (((ctx.alphaCenter ^ 2 + ctx.totalWeight + ctx.fgAnchorWeight) * background b) -
      ctx.alphaCenter * (1 - ctx.alphaCenter) * foreground b) / det
  ]

@[simp] theorem foreground_closedFormSolution (ctx : AnchoredLocalContext ι) :
    foreground (closedFormSolution ctx) =
      closedFormForegroundNumerator ctx / closedFormDenom ctx := by
  simp [closedFormSolution, closedFormForegroundNumerator, foreground, background]

@[simp] theorem background_closedFormSolution (ctx : AnchoredLocalContext ι) :
    background (closedFormSolution ctx) =
      closedFormBackgroundNumerator ctx / closedFormDenom ctx := by
  simp [closedFormSolution, closedFormBackgroundNumerator, foreground, background]

end AnchoredLocalContext

end FastMLFE2.Core
