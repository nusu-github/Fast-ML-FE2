import FastMLFE2.Assumptions.Bundles
import FastMLFE2.Canonical.Grid

namespace FastMLFE2.Assumptions

open FastMLFE2.Canonical

class GridMathAssumptions {h w : Nat} (data : GridPixelData h w) : Prop where
  epsilonPos : 0 < data.epsilonR
  omegaNonneg : 0 ≤ data.omega
  alphaBounded : ∀ p, 0 ≤ data.alpha p ∧ data.alpha p ≤ 1

end FastMLFE2.Assumptions
