import Mathlib

namespace FastMLFE2.Theorems

open scoped BigOperators

namespace Quantization

/-- Quantize a real number down to the grid `{k / S}`. -/
noncomputable def gridQuantize (S : ℕ) (x : ℝ) : ℝ :=
  Int.floor (x * S) / S

/-- Finite geometric series with ratio `ρ`. -/
def geomSeries (ρ : ℝ) (n : ℕ) : ℝ :=
  (Finset.range n).sum fun k => ρ ^ k

theorem gridQuantize_le
    {S : ℕ} (hS : 0 < S) (x : ℝ) :
    gridQuantize S x ≤ x := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hfloor : (Int.floor (x * S) : ℝ) ≤ x * S := Int.floor_le (x * S)
  exact (div_le_iff₀ hS').2 (by
    simpa [gridQuantize, mul_comm, mul_left_comm, mul_assoc] using hfloor)

theorem lt_gridQuantize_add_one_div
    {S : ℕ} (hS : 0 < S) (x : ℝ) :
    x < gridQuantize S x + 1 / S := by
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have hlt : x * S < Int.floor (x * S) + 1 := Int.lt_floor_add_one (x * S)
  have h' : x < (Int.floor (x * S) + 1) / S := by
    exact (lt_div_iff₀ hS').2 hlt
  simpa [gridQuantize, add_div, add_comm, add_left_comm, add_assoc, mul_comm,
    mul_left_comm, mul_assoc] using h'

theorem abs_gridQuantize_sub_lt
    {S : ℕ} (hS : 0 < S) (x : ℝ) :
    |gridQuantize S x - x| < 1 / S := by
  have hle := gridQuantize_le (S := S) hS x
  have hlt := lt_gridQuantize_add_one_div (S := S) hS x
  have hnonneg : 0 ≤ x - gridQuantize S x := by
    linarith
  rw [abs_sub_comm, abs_of_nonneg hnonneg]
  linarith

theorem lt_of_quantization_margin_left
    {x q τ δ : ℝ}
    (hqx : |q - x| ≤ δ)
    (hx : x + δ < τ) :
    q < τ := by
  have hq : q ≤ x + δ := by
    have h' := abs_le.mp hqx
    linarith
  linarith

theorem lt_of_quantization_margin_right
    {x q τ δ : ℝ}
    (hqx : |q - x| ≤ δ)
    (hx : τ + δ < x) :
    τ < q := by
  have hq : x - δ ≤ q := by
    have h' := abs_le.mp hqx
    linarith
  linarith

theorem oneStepPerturbation_error_le
    {α : Type*} [PseudoMetricSpace α]
    (T A q : α → α)
    {ρ ε δ : ℝ}
    (hρ : 0 ≤ ρ)
    (hApprox : ∀ x, dist (A x) (T x) ≤ ε)
    (hLip : ∀ x y, dist (T x) (T y) ≤ ρ * dist x y)
    (hq : ∀ x, dist (q x) x ≤ δ)
    (x : α) :
    dist (A (q x)) (T x) ≤ ε + ρ * δ := by
  calc
    dist (A (q x)) (T x)
        ≤ dist (A (q x)) (T (q x)) + dist (T (q x)) (T x) := dist_triangle _ _ _
    _ ≤ ε + ρ * δ := by
      nlinarith [hApprox (q x), hLip (q x) x, hq x, hρ]

theorem geomSeries_succ
    (ρ : ℝ) (n : ℕ) :
    1 + ρ * geomSeries ρ n = geomSeries ρ (n + 1) := by
  simpa [geomSeries, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    (geom_sum_succ (x := ρ) (n := n)).symm

theorem geomSeries_le_inv_one_sub
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∀ n, geomSeries ρ n ≤ 1 / (1 - ρ) := by
  intro n
  induction n with
  | zero =>
      have hden : 0 < 1 - ρ := by linarith
      have hnonneg : 0 ≤ 1 / (1 - ρ) := by
        exact div_nonneg (by positivity) (le_of_lt hden)
      simpa [geomSeries] using hnonneg
  | succ n ih =>
      have hmul : ρ * geomSeries ρ n ≤ ρ * (1 / (1 - ρ)) :=
        mul_le_mul_of_nonneg_left (ih) hρ
      have hstep : 1 + ρ * (1 / (1 - ρ)) = 1 / (1 - ρ) := by
        have hden : 1 - ρ ≠ 0 := by linarith
        field_simp [hden]
        ring
      calc
        geomSeries ρ (n + 1) = 1 + ρ * geomSeries ρ n := by
          rw [geomSeries_succ]
        _ ≤ 1 + ρ * (1 / (1 - ρ)) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul 1
        _ = 1 / (1 - ρ) := hstep

theorem iteratePerturbation_error_le_geom_sum
    {α : Type*} [PseudoMetricSpace α]
    (T P : α → α)
    {ρ ε : ℝ}
    (hρ : 0 ≤ ρ)
    (hT : ∀ x y, dist (T x) (T y) ≤ ρ * dist x y)
    (hP : ∀ x, dist (P x) (T x) ≤ ε) :
    ∀ n x, dist (Nat.iterate P n x) (Nat.iterate T n x) ≤
      ε * geomSeries ρ n := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [geomSeries]
  | succ n ih =>
      intro x
      have hPsucc : Nat.iterate P (n + 1) x = P (Nat.iterate P n x) := by
        simpa using (Function.iterate_succ_apply' P n x)
      have hTsucc : Nat.iterate T (n + 1) x = T (Nat.iterate T n x) := by
        simpa using (Function.iterate_succ_apply' T n x)
      rw [hPsucc, hTsucc]
      calc
        dist (P (Nat.iterate P n x)) (T (Nat.iterate T n x))
            ≤ dist (P (Nat.iterate P n x)) (T (Nat.iterate P n x)) +
                dist (T (Nat.iterate P n x)) (T (Nat.iterate T n x)) := by
              exact dist_triangle _ _ _
        _ ≤ ε + ρ * (ε * geomSeries ρ n) := by
              have hleft : dist (P (Nat.iterate P n x)) (T (Nat.iterate P n x)) ≤ ε :=
                hP (Nat.iterate P n x)
              have hright :
                  dist (T (Nat.iterate P n x)) (T (Nat.iterate T n x)) ≤
                    ρ * (ε * geomSeries ρ n) := by
                exact le_trans
                  (hT (Nat.iterate P n x) (Nat.iterate T n x))
                  (mul_le_mul_of_nonneg_left (ih x) hρ)
              exact add_le_add hleft hright
        _ = ε * geomSeries ρ (n + 1) := by
              calc
                ε + ρ * (ε * geomSeries ρ n)
                    = ε * (1 + ρ * geomSeries ρ n) := by ring
                _ = ε * geomSeries ρ (n + 1) := by
                      rw [geomSeries_succ]

theorem iteratePerturbation_error_le_inv_one_sub
    {α : Type*} [PseudoMetricSpace α]
    (T P : α → α)
    {ρ ε : ℝ}
    (hρ : 0 ≤ ρ)
    (hρ1 : ρ < 1)
    (hT : ∀ x y, dist (T x) (T y) ≤ ρ * dist x y)
    (hP : ∀ x, dist (P x) (T x) ≤ ε)
    (hε : 0 ≤ ε) :
    ∀ n x, dist (Nat.iterate P n x) (Nat.iterate T n x) ≤
      ε / (1 - ρ) := by
  intro n x
  have hsum := iteratePerturbation_error_le_geom_sum
    (T := T) (P := P) (ρ := ρ) (ε := ε) hρ hT hP n x
  have hgeom : geomSeries ρ n ≤ 1 / (1 - ρ) :=
    geomSeries_le_inv_one_sub (ρ := ρ) hρ hρ1 n
  have hmul : ε * geomSeries ρ n ≤ ε / (1 - ρ) := by
    have hmul' := mul_le_mul_of_nonneg_left hgeom hε
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul'
  exact le_trans hsum hmul

end Quantization

end FastMLFE2.Theorems
