import FastMLFE2.Theory.Theorems.BinaryAlpha

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Core
open FastMLFE2.Theory.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

theorem localCost_eq_of_alpha_zero
    (ctx : LocalContext ι)
    (g : LocalUnknown)
    (hα : ctx.alphaCenter = 0) :
    ctx.localCost g =
      (background g - ctx.imageValue) ^ 2 +
        ∑ j, ctx.neighborWeight j *
          ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) := by
  simp [FastMLFE2.Theory.Core.LocalContext.localCost,
    FastMLFE2.Theory.Core.LocalContext.compositingResidual_eq, hα]

theorem localCost_eq_of_alpha_one
    (ctx : LocalContext ι)
    (g : LocalUnknown)
    (hα : ctx.alphaCenter = 1) :
    ctx.localCost g =
      (foreground g - ctx.imageValue) ^ 2 +
        ∑ j, ctx.neighborWeight j *
          ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) := by
  simp [FastMLFE2.Theory.Core.LocalContext.localCost,
    FastMLFE2.Theory.Core.LocalContext.compositingResidual_eq, hα]

theorem isCostStationary_iff_of_alpha_zero
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (g : LocalUnknown)
    (hα : ctx.alphaCenter = 0) :
    ctx.IsCostStationary g ↔
      ctx.totalWeight * foreground g = ctx.foregroundSum ∧
        (1 + ctx.totalWeight) * background g = ctx.imageValue + ctx.backgroundSum := by
  rw [isCostStationary_iff_solvesNormalEquation]
  have hrhs0 : ctx.rhs 0 = ctx.foregroundSum := by
    simpa [foreground, background, mkLocalUnknown] using
      congrFun (rhs_eq_of_alpha_zero (ctx := ctx) hα) 0
  have hrhs1 : ctx.rhs 1 = ctx.imageValue + ctx.backgroundSum := by
    simpa [foreground, background, mkLocalUnknown] using
      congrFun (rhs_eq_of_alpha_zero (ctx := ctx) hα) 1
  constructor
  · intro hsolve
    constructor
    · have hfg : ctx.normalMatrix.mulVec g 0 = ctx.rhs 0 := by
        simpa using congrFun hsolve 0
      calc
        ctx.totalWeight * foreground g = ctx.rhs 0 := by
          simpa [FastMLFE2.Theory.Core.LocalContext.normalMatrix_mulVec_foreground, hα] using hfg
        _ = ctx.foregroundSum := hrhs0
    · have hbg : ctx.normalMatrix.mulVec g 1 = ctx.rhs 1 := by
        simpa using congrFun hsolve 1
      calc
        (1 + ctx.totalWeight) * background g = ctx.rhs 1 := by
          simpa [FastMLFE2.Theory.Core.LocalContext.normalMatrix_mulVec_background, hα] using hbg
        _ = ctx.imageValue + ctx.backgroundSum := hrhs1
  · rintro ⟨hfg, hbg⟩
    funext i
    fin_cases i
    · calc
        ctx.normalMatrix.mulVec g 0 = ctx.totalWeight * foreground g := by
          simp [FastMLFE2.Theory.Core.LocalContext.normalMatrix_mulVec_foreground, hα]
        _ = ctx.foregroundSum := hfg
        _ = ctx.rhs 0 := hrhs0.symm
    · calc
        ctx.normalMatrix.mulVec g 1 = (1 + ctx.totalWeight) * background g := by
          simp [FastMLFE2.Theory.Core.LocalContext.normalMatrix_mulVec_background, hα]
        _ = ctx.imageValue + ctx.backgroundSum := hbg
        _ = ctx.rhs 1 := hrhs1.symm

theorem isCostStationary_iff_of_alpha_one
    (ctx : LocalContext ι)
    [CoreMathAssumptions ctx]
    (g : LocalUnknown)
    (hα : ctx.alphaCenter = 1) :
    ctx.IsCostStationary g ↔
      (1 + ctx.totalWeight) * foreground g = ctx.imageValue + ctx.foregroundSum ∧
        ctx.totalWeight * background g = ctx.backgroundSum := by
  rw [isCostStationary_iff_solvesNormalEquation]
  have hrhs0 : ctx.rhs 0 = ctx.imageValue + ctx.foregroundSum := by
    simpa [foreground, background, mkLocalUnknown] using
      congrFun (rhs_eq_of_alpha_one (ctx := ctx) hα) 0
  have hrhs1 : ctx.rhs 1 = ctx.backgroundSum := by
    simpa [foreground, background, mkLocalUnknown] using
      congrFun (rhs_eq_of_alpha_one (ctx := ctx) hα) 1
  constructor
  · intro hsolve
    constructor
    · have hfg : ctx.normalMatrix.mulVec g 0 = ctx.rhs 0 := by
        simpa using congrFun hsolve 0
      calc
        (1 + ctx.totalWeight) * foreground g = ctx.rhs 0 := by
          simpa [FastMLFE2.Theory.Core.LocalContext.normalMatrix_mulVec_foreground, hα] using hfg
        _ = ctx.imageValue + ctx.foregroundSum := hrhs0
    · have hbg : ctx.normalMatrix.mulVec g 1 = ctx.rhs 1 := by
        simpa using congrFun hsolve 1
      calc
        ctx.totalWeight * background g = ctx.rhs 1 := by
          simpa [FastMLFE2.Theory.Core.LocalContext.normalMatrix_mulVec_background, hα] using hbg
        _ = ctx.backgroundSum := hrhs1
  · rintro ⟨hfg, hbg⟩
    funext i
    fin_cases i
    · calc
        ctx.normalMatrix.mulVec g 0 = (1 + ctx.totalWeight) * foreground g := by
          simp [FastMLFE2.Theory.Core.LocalContext.normalMatrix_mulVec_foreground, hα]
        _ = ctx.imageValue + ctx.foregroundSum := hfg
        _ = ctx.rhs 0 := hrhs0.symm
    · calc
        ctx.normalMatrix.mulVec g 1 = ctx.totalWeight * background g := by
          simp [FastMLFE2.Theory.Core.LocalContext.normalMatrix_mulVec_background, hα]
        _ = ctx.backgroundSum := hbg
        _ = ctx.rhs 1 := hrhs1.symm

example (ctx : LocalContext ι) (g : LocalUnknown) (hα : ctx.alphaCenter = 0) :
    ctx.localCost g =
      (background g - ctx.imageValue) ^ 2 +
        ∑ j, ctx.neighborWeight j *
          ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) := by
  simpa using localCost_eq_of_alpha_zero (ctx := ctx) g hα

example (ctx : LocalContext ι) (g : LocalUnknown) (hα : ctx.alphaCenter = 1) :
    ctx.localCost g =
      (foreground g - ctx.imageValue) ^ 2 +
        ∑ j, ctx.neighborWeight j *
          ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) := by
  simpa using localCost_eq_of_alpha_one (ctx := ctx) g hα

example (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (g : LocalUnknown) (hα : ctx.alphaCenter = 0) :
    ctx.IsCostStationary g ↔
      ctx.totalWeight * foreground g = ctx.foregroundSum ∧
        (1 + ctx.totalWeight) * background g = ctx.imageValue + ctx.backgroundSum := by
  simpa using isCostStationary_iff_of_alpha_zero (ctx := ctx) g hα

end LocalContext

end FastMLFE2.Theory.Theorems
