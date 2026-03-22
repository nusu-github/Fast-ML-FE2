import FastMLFE2.Theory.Core.LocalEquation

namespace FastMLFE2.Theory.Core

/-!
Denotational local semantics for the refounded theory kernel.

This layer intentionally stops at the local normal equation and its solution relation.
Derivative-based stationary theorems are deferred until the cost-to-normal-equation bridge is
proved explicitly. In particular, this file does not define a surrogate such as the old
`halfGradient`.
-/

variable {ι : Type*} [Fintype ι]

namespace LocalContext

abbrev Ctx (ι : Type*) := _root_.FastMLFE2.Theory.Core.LocalContext ι

abbrev Unknown := _root_.FastMLFE2.Theory.Core.LocalUnknown

def SolvesNormalEquation (ctx : Ctx ι) (g : Unknown) : Prop :=
  ctx.normalMatrix.mulVec g = ctx.rhs

def IsLocalSolution (ctx : Ctx ι) (g : Unknown) : Prop :=
  SolvesNormalEquation ctx g

@[simp] theorem totalWeight_eq_sum_neighborWeight (ctx : Ctx ι) :
    ctx.totalWeight = ∑ j, ctx.neighborWeight j := rfl

@[simp] theorem foregroundSum_eq_sum_neighborWeight_mul (ctx : Ctx ι) :
    ctx.foregroundSum = ∑ j, ctx.neighborWeight j * ctx.fgNeighbor j := rfl

@[simp] theorem backgroundSum_eq_sum_neighborWeight_mul (ctx : Ctx ι) :
    ctx.backgroundSum = ∑ j, ctx.neighborWeight j * ctx.bgNeighbor j := rfl

@[simp] theorem solvesNormalEquation_iff (ctx : Ctx ι) (g : Unknown) :
    ctx.SolvesNormalEquation g ↔ ctx.normalMatrix.mulVec g = ctx.rhs := Iff.rfl

@[simp] theorem isLocalSolution_iff (ctx : Ctx ι) (g : Unknown) :
    ctx.IsLocalSolution g ↔ ctx.normalMatrix.mulVec g = ctx.rhs := Iff.rfl

end LocalContext

end FastMLFE2.Theory.Core
