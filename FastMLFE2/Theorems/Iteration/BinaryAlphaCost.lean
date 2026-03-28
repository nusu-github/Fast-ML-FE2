import FastMLFE2.Theorems.Iteration.BinaryAlpha

namespace FastMLFE2.Theorems

open FastMLFE2.Core
open FastMLFE2.Assumptions

namespace LocalContext

variable {ι : Type*} [Fintype ι]

theorem localCost_eq_of_alpha_zero
    (ctx : LocalContext ι) (g : LocalUnknown) (hα : ctx.alphaCenter = 0) :
    ctx.localCost g =
      (background g - ctx.imageValue) ^ 2 +
        ∑ j, ctx.neighborWeight j *
          ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) := by
  simp [LocalContext.localCost, LocalContext.compositingResidual_eq, hα]

theorem localCost_eq_of_alpha_one
    (ctx : LocalContext ι) (g : LocalUnknown) (hα : ctx.alphaCenter = 1) :
    ctx.localCost g =
      (foreground g - ctx.imageValue) ^ 2 +
        ∑ j, ctx.neighborWeight j *
          ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) := by
  simp [LocalContext.localCost, LocalContext.compositingResidual_eq, hα]

theorem isCostStationary_iff_of_alpha_zero
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (g : LocalUnknown) (hα : ctx.alphaCenter = 0) :
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
    exact ⟨by simpa [LocalContext.normalMatrix_mulVec_foreground, hα, hrhs0] using
              congrFun hsolve 0,
           by simpa [LocalContext.normalMatrix_mulVec_background, hα, hrhs1] using
              congrFun hsolve 1⟩
  · rintro ⟨hfg, hbg⟩
    funext i; fin_cases i
    · simpa [LocalContext.normalMatrix_mulVec_foreground, hα, hrhs0] using hfg
    · simpa [LocalContext.normalMatrix_mulVec_background, hα, hrhs1] using hbg

theorem isCostStationary_iff_of_alpha_one
    (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (g : LocalUnknown) (hα : ctx.alphaCenter = 1) :
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
    exact ⟨by simpa [LocalContext.normalMatrix_mulVec_foreground, hα, hrhs0] using
              congrFun hsolve 0,
           by simpa [LocalContext.normalMatrix_mulVec_background, hα, hrhs1] using
              congrFun hsolve 1⟩
  · rintro ⟨hfg, hbg⟩
    funext i; fin_cases i
    · simpa [LocalContext.normalMatrix_mulVec_foreground, hα, hrhs0] using hfg
    · simpa [LocalContext.normalMatrix_mulVec_background, hα, hrhs1] using hbg

example (ctx : LocalContext ι) (g : LocalUnknown) (hα : ctx.alphaCenter = 0) :
    ctx.localCost g =
      (background g - ctx.imageValue) ^ 2 +
        ∑ j, ctx.neighborWeight j *
          ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) :=
  localCost_eq_of_alpha_zero ctx g hα

example (ctx : LocalContext ι) (g : LocalUnknown) (hα : ctx.alphaCenter = 1) :
    ctx.localCost g =
      (foreground g - ctx.imageValue) ^ 2 +
        ∑ j, ctx.neighborWeight j *
          ((foreground g - ctx.fgNeighbor j) ^ 2 + (background g - ctx.bgNeighbor j) ^ 2) :=
  localCost_eq_of_alpha_one ctx g hα

example (ctx : LocalContext ι) [CoreMathAssumptions ctx]
    (g : LocalUnknown) (hα : ctx.alphaCenter = 0) :
    ctx.IsCostStationary g ↔
      ctx.totalWeight * foreground g = ctx.foregroundSum ∧
        (1 + ctx.totalWeight) * background g = ctx.imageValue + ctx.backgroundSum :=
  isCostStationary_iff_of_alpha_zero ctx g hα

end LocalContext

end FastMLFE2.Theorems
