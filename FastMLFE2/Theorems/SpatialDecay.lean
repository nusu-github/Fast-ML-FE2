import FastMLFE2.Level.Locality
import Mathlib

namespace FastMLFE2.Theorems

open FastMLFE2.Level

namespace SpatialDecay

/-- Abstract radius-indexed neighborhoods used by the decay/halo interfaces. -/
structure RadiusFamily (κ : Type*) where
  ball : Nat → κ → Finset κ

/-- A fixed-exterior relation: two states agree outside a chosen region. -/
def FixedOutside {κ : Type*} (Ω : Finset κ) (state₁ state₂ : PixelState κ) : Prop :=
  ∀ q, q ∉ Ω → state₁ q = state₂ q

/--
Abstract exponential decay interface for a response map.

The bound is stated against an arbitrary radius family, so later work can instantiate it with a
geometric metric ball, a halo expansion rule, or a problem-specific influence stencil.
-/
structure RadiusDecay {κ : Type*} {α : Type*} [NormedAddCommGroup α]
    (balls : RadiusFamily κ) (response : PixelState κ → κ → α) where
  C : ℝ
  rho : ℝ
  hC : 0 ≤ C
  hrho_nonneg : 0 ≤ rho
  hrho_lt_one : rho < 1
  bound :
    ∀ p state₁ state₂ R,
      StateEqOn (balls.ball R p) state₁ state₂ →
        ‖response state₁ p - response state₂ p‖ ≤ C * rho ^ R

/-- Exponential envelopes decrease as the radius increases. -/
theorem decayEnvelope_antitone {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    {R S : Nat} (hRS : R ≤ S) :
    C * rho ^ S ≤ C * rho ^ R := by
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hrho hrho1 hRS) hC

/-- A stronger agreement radius yields the weaker `R`-level exponential bound. -/
theorem RadiusDecay.bound_of_radius_le
    {κ : Type*} {α : Type*} [NormedAddCommGroup α]
    {balls : RadiusFamily κ} {response : PixelState κ → κ → α}
    (h : RadiusDecay balls response) {p : κ} {state₁ state₂ : PixelState κ}
    {R S : Nat} (hRS : R ≤ S)
    (hEqS : StateEqOn (balls.ball S p) state₁ state₂) :
    ‖response state₁ p - response state₂ p‖ ≤ h.C * h.rho ^ R := by
  have hbase := h.bound p state₁ state₂ S hEqS
  exact hbase.trans
    (decayEnvelope_antitone h.hC h.hrho_nonneg (le_of_lt h.hrho_lt_one) hRS)

/--
Halo-width interface for interior-only approximations.

`agreeOnHalo` is the abstract lemma one would instantiate from a geometric fixed-exterior model:
if the outside region is fixed, then the two states agree on the halo needed to control the
interior pixel.
-/
structure HaloDecay {κ : Type*} {α : Type*} [NormedAddCommGroup α]
    (balls : RadiusFamily κ) (response : PixelState κ → κ → α) where
  radiusDecay : RadiusDecay balls response
  haloWidth : κ → Finset κ → Nat
  agreeOnHalo :
    ∀ p Ω state₁ state₂,
      p ∈ Ω →
      FixedOutside Ω state₁ state₂ →
      StateEqOn (balls.ball (haloWidth p Ω) p) state₁ state₂

/-- Proposition 6: a fixed-exterior interior-only approximation is controlled by halo width. -/
theorem HaloDecay.bound
    {κ : Type*} {α : Type*} [NormedAddCommGroup α]
    {balls : RadiusFamily κ} {response : PixelState κ → κ → α}
    (h : HaloDecay balls response) {p : κ} {Ω : Finset κ}
    {state₁ state₂ : PixelState κ} (hp : p ∈ Ω)
    (hfix : FixedOutside Ω state₁ state₂) :
    ‖response state₁ p - response state₂ p‖ ≤
      h.radiusDecay.C * h.radiusDecay.rho ^ h.haloWidth p Ω := by
  exact h.radiusDecay.bound p state₁ state₂ (h.haloWidth p Ω)
    (h.agreeOnHalo p Ω state₁ state₂ hp hfix)

/-- Smaller halo widths inherit the same exponential envelope. -/
theorem HaloDecay.bound_of_smaller_radius
    {κ : Type*} {α : Type*} [NormedAddCommGroup α]
    {balls : RadiusFamily κ} {response : PixelState κ → κ → α}
    (h : HaloDecay balls response) {p : κ} {Ω : Finset κ}
    {state₁ state₂ : PixelState κ} (hp : p ∈ Ω)
    (hfix : FixedOutside Ω state₁ state₂) {R : Nat}
    (hR : R ≤ h.haloWidth p Ω) :
    ‖response state₁ p - response state₂ p‖ ≤ h.radiusDecay.C * h.radiusDecay.rho ^ R := by
  have hbase := h.bound hp hfix
  exact hbase.trans
    (decayEnvelope_antitone h.radiusDecay.hC h.radiusDecay.hrho_nonneg
      (le_of_lt h.radiusDecay.hrho_lt_one) hR)

end SpatialDecay

end FastMLFE2.Theorems
