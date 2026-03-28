import FastMLFE2.Canonical.Grid

namespace FastMLFE2.Theorems

open FastMLFE2.Canonical

theorem nonempty_validDir_of_isInterior
    {h w : Nat} (p : Pixel h w) (hInterior : IsInterior p) :
    Nonempty (ValidDir p) :=
  ⟨⟨.up, hInterior.1⟩⟩

theorem nonempty_validDir_of_isTopEdgeNoncorner
    {h w : Nat} (p : Pixel h w) (hTop : IsTopEdgeNoncorner p) :
    Nonempty (ValidDir p) :=
  ⟨⟨.down, hTop.2.1⟩⟩

theorem nonempty_validDir_of_isBottomEdgeNoncorner
    {h w : Nat} (p : Pixel h w) (hBottom : IsBottomEdgeNoncorner p) :
    Nonempty (ValidDir p) :=
  ⟨⟨.up, hBottom.1⟩⟩

theorem nonempty_validDir_of_isLeftEdgeNoncorner
    {h w : Nat} (p : Pixel h w) (hLeft : IsLeftEdgeNoncorner p) :
    Nonempty (ValidDir p) :=
  ⟨⟨.right, hLeft.2.2.2⟩⟩

theorem nonempty_validDir_of_isRightEdgeNoncorner
    {h w : Nat} (p : Pixel h w) (hRight : IsRightEdgeNoncorner p) :
    Nonempty (ValidDir p) :=
  ⟨⟨.left, hRight.2.2.1⟩⟩

theorem nonempty_validDir_of_isTopLeftCorner
    {h w : Nat} [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w) (hCorner : IsTopLeftCorner p) :
    Nonempty (ValidDir p) :=
  ⟨⟨.down, by
    have := Fact.out (p := 2 ≤ h)
    simpa [IsValidDir, hCorner.1] using (show 1 < h by omega)⟩⟩

theorem nonempty_validDir_of_isTopRightCorner
    {h w : Nat} [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w) (hCorner : IsTopRightCorner p) :
    Nonempty (ValidDir p) :=
  ⟨⟨.down, by
    have := Fact.out (p := 2 ≤ h)
    simpa [IsValidDir, hCorner.1] using (show 1 < h by omega)⟩⟩

theorem nonempty_validDir_of_isBottomLeftCorner
    {h w : Nat} [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w) (hCorner : IsBottomLeftCorner p) :
    Nonempty (ValidDir p) :=
  ⟨⟨.up, by
    rcases hCorner with ⟨hB, _⟩
    simp [IsValidDir]; have : 2 ≤ h := Fact.out; omega⟩⟩

theorem nonempty_validDir_of_isBottomRightCorner
    {h w : Nat} [Fact (2 ≤ h)] [Fact (2 ≤ w)]
    (p : Pixel h w) (hCorner : IsBottomRightCorner p) :
    Nonempty (ValidDir p) :=
  ⟨⟨.up, by
    rcases hCorner with ⟨hB, _⟩
    simp [IsValidDir]; have : 2 ≤ h := Fact.out; omega⟩⟩

end FastMLFE2.Theorems
