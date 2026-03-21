import Mathlib

namespace FastMLFE2

/-- The two coordinates of a local unknown correspond to foreground and background. -/
abbrev FBIdx := Fin 2

/-- A local color vector `(F_i^c, B_i^c)`. -/
abbrev FBVec := FBIdx → ℝ

def mkFBVec (foreground background : ℝ) : FBVec := ![foreground, background]

def foreground (g : FBVec) : ℝ := g 0

def background (g : FBVec) : ℝ := g 1

/-- The compositing weights `[α, 1 - α]`. -/
def uVec (α : ℝ) : FBVec := ![α, 1 - α]

@[simp] theorem foreground_mkFBVec (f b : ℝ) : foreground (mkFBVec f b) = f := by
  simp [foreground, mkFBVec]

@[simp] theorem background_mkFBVec (f b : ℝ) : background (mkFBVec f b) = b := by
  simp [background, mkFBVec]

@[simp] theorem foreground_uVec (α : ℝ) : foreground (uVec α) = α := by
  simp [foreground, uVec]

@[simp] theorem background_uVec (α : ℝ) : background (uVec α) = 1 - α := by
  simp [background, uVec]

@[simp] theorem vecHead_eq_foreground (g : FBVec) : Matrix.vecHead g = foreground g := rfl

@[simp] theorem vecHead_vecTail_eq_background (g : FBVec) :
    Matrix.vecHead (Matrix.vecTail g) = background g := rfl

theorem ext_fbVec {g h : FBVec}
    (hfg : foreground g = foreground h)
    (hbg : background g = background h) : g = h := by
  ext i
  fin_cases i
  · simpa [foreground] using hfg
  · simpa [background] using hbg

end FastMLFE2
