import FastMLFE2.FixedPrecision.Format
import FastMLFE2.Theorems.QuantizationBounds

namespace FastMLFE2.FixedPrecision

open FastMLFE2.Theorems

variable {cfg : FixedFormat}

structure ReciprocalTableSpec (cfg : FixedFormat) where
  weightDenomMin : Nat := cfg.scale
  weightDenomMax : Nat := 4 * (cfg.weightScale + cfg.scale)
  gainDenomMin : Nat := cfg.scale * cfg.scale
  gainDenomMax : Nat := cfg.scale * (4 * (cfg.weightScale + cfg.scale)) + 2 * cfg.scale * cfg.scale
  deriving Repr

def inWeightDomain (tbl : ReciprocalTableSpec cfg) (denom : Nat) : Prop :=
  tbl.weightDenomMin ≤ denom ∧ denom ≤ tbl.weightDenomMax

def inGainDomain (tbl : ReciprocalTableSpec cfg) (denom : Nat) : Prop :=
  tbl.gainDenomMin ≤ denom ∧ denom ≤ tbl.gainDenomMax

noncomputable def weightReciprocalCoeff
    (cfg : FixedFormat) (denom : Nat) : Coefficient cfg :=
  encodeScaledRatioFloor cfg cfg.scale denom

noncomputable def gainReciprocalCoeff
    (cfg : FixedFormat) (denom : Nat) : Coefficient cfg :=
  encodeScaledRatioFloor cfg (cfg.scale * cfg.scale) denom

def coefficientQuantizationBudget (cfg : FixedFormat) : ℚ :=
  1 / coeffScale cfg

theorem coefficientQuantizationBudget_nonneg (cfg : FixedFormat) :
    0 ≤ coefficientQuantizationBudget cfg := by
  have hNat : 0 < coeffScale cfg := by
    simp [coeffScale]
  have hRat : (0 : ℚ) < coeffScale cfg := by
    exact_mod_cast hNat
  have hLe : 0 ≤ (coeffScale cfg : ℚ) := le_of_lt hRat
  simp [coefficientQuantizationBudget, hLe]

theorem inWeightDomain_of_bounds
    (tbl : ReciprocalTableSpec cfg)
    {denom : Nat}
    (hmin : tbl.weightDenomMin ≤ denom)
    (hmax : denom ≤ tbl.weightDenomMax) :
    inWeightDomain tbl denom := ⟨hmin, hmax⟩

theorem inGainDomain_of_bounds
    (tbl : ReciprocalTableSpec cfg)
    {denom : Nat}
    (hmin : tbl.gainDenomMin ≤ denom)
    (hmax : denom ≤ tbl.gainDenomMax) :
    inGainDomain tbl denom := ⟨hmin, hmax⟩

end FastMLFE2.FixedPrecision
