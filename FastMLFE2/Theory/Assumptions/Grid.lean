import FastMLFE2.Theory.Assumptions.Bundles
import FastMLFE2.Theory.Canonical.Grid

namespace FastMLFE2.Theory.Assumptions

open FastMLFE2.Theory.Canonical

class GridMathAssumptions {h w : Nat} (data : GridPixelData h w) : Prop where
  epsilonPos : 0 < data.epsilonR
  omegaNonneg : 0 ≤ data.omega
  alphaBounded : ∀ p, 0 ≤ data.alpha p ∧ data.alpha p ≤ 1

end FastMLFE2.Theory.Assumptions
