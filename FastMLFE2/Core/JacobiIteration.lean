import FastMLFE2.Core.LocalEquation

namespace FastMLFE2.Core

/-!
Per-pixel Jacobi iteration definitions for the 2×2 local system.

These definitions are separated from the convergence theorems (in `Theorems.JacobiContraction`)
so that they can be referenced without importing the theorem layer.
-/

namespace LocalContext

variable {ι : Type*} [Fintype ι]

def jacobiDiagForeground (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter ^ 2 + ctx.totalWeight

def jacobiDiagBackground (ctx : LocalContext ι) : ℝ :=
  (1 - ctx.alphaCenter) ^ 2 + ctx.totalWeight

def jacobiCrossTerm (ctx : LocalContext ι) : ℝ :=
  ctx.alphaCenter * (1 - ctx.alphaCenter)

noncomputable def jacobiForegroundCoeff (ctx : LocalContext ι) : ℝ :=
  jacobiCrossTerm ctx / jacobiDiagForeground ctx

noncomputable def jacobiBackgroundCoeff (ctx : LocalContext ι) : ℝ :=
  jacobiCrossTerm ctx / jacobiDiagBackground ctx

noncomputable def jacobiStep (ctx : LocalContext ι) (g : LocalUnknown) : LocalUnknown :=
  mkLocalUnknown
    ((foreground ctx.rhs - jacobiCrossTerm ctx * background g) / jacobiDiagForeground ctx)
    ((background ctx.rhs - jacobiCrossTerm ctx * foreground g) / jacobiDiagBackground ctx)

noncomputable def jacobiDifferenceMap (ctx : LocalContext ι) (g : LocalUnknown) : LocalUnknown :=
  mkLocalUnknown
    (-(jacobiForegroundCoeff ctx) * background g)
    (-(jacobiBackgroundCoeff ctx) * foreground g)

def localInfinityNorm (g : LocalUnknown) : ℝ :=
  max |foreground g| |background g|

noncomputable def jacobiSpectralRadiusSq (ctx : LocalContext ι) : ℝ :=
  jacobiForegroundCoeff ctx * jacobiBackgroundCoeff ctx

noncomputable def jacobiSpectralRadius (ctx : LocalContext ι) : ℝ :=
  jacobiCrossTerm ctx / Real.sqrt (jacobiDiagForeground ctx * jacobiDiagBackground ctx)

noncomputable def jacobiIterate (ctx : LocalContext ι) (k : Nat) : LocalUnknown → LocalUnknown :=
  Nat.iterate (jacobiStep ctx) k

noncomputable def jacobiOneStepGain (ctx : LocalContext ι) : ℝ :=
  max (jacobiForegroundCoeff ctx) (jacobiBackgroundCoeff ctx)

@[simp] theorem jacobiStep_foreground (ctx : LocalContext ι) (g : LocalUnknown) :
    foreground (jacobiStep ctx g) =
      (foreground ctx.rhs - jacobiCrossTerm ctx * background g) / jacobiDiagForeground ctx := by
  simp [jacobiStep]

@[simp] theorem jacobiStep_background (ctx : LocalContext ι) (g : LocalUnknown) :
    background (jacobiStep ctx g) =
      (background ctx.rhs - jacobiCrossTerm ctx * foreground g) / jacobiDiagBackground ctx := by
  simp [jacobiStep]

@[simp] theorem jacobiDifferenceMap_foreground (ctx : LocalContext ι) (g : LocalUnknown) :
    foreground (jacobiDifferenceMap ctx g) = -(jacobiForegroundCoeff ctx) * background g := by
  simp [jacobiDifferenceMap]

@[simp] theorem jacobiDifferenceMap_background (ctx : LocalContext ι) (g : LocalUnknown) :
    background (jacobiDifferenceMap ctx g) = -(jacobiBackgroundCoeff ctx) * foreground g := by
  simp [jacobiDifferenceMap]

@[simp] theorem jacobiIterate_zero (ctx : LocalContext ι) (x : LocalUnknown) :
    jacobiIterate ctx 0 x = x := rfl

@[simp] theorem jacobiIterate_succ (ctx : LocalContext ι) (k : Nat) (x : LocalUnknown) :
    jacobiIterate ctx (k + 1) x = jacobiIterate ctx k (jacobiStep ctx x) := by
  simp [jacobiIterate, Function.iterate_succ_apply]

end LocalContext

end FastMLFE2.Core
