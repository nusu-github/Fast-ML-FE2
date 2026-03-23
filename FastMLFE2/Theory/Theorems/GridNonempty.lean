import FastMLFE2.Theory.Canonical.Grid

namespace FastMLFE2.Theory.Theorems

open FastMLFE2.Theory.Canonical

theorem nonempty_validDir_of_isInterior
    {h w : Nat}
    (p : Pixel h w)
    (hInterior : IsInterior p) :
    Nonempty (ValidDir p) := by
  rcases hInterior with ⟨hUp, _, _, _⟩
  exact ⟨⟨Direction4.up, hUp⟩⟩

theorem nonempty_validDir_of_isTopEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hTop : IsTopEdgeNoncorner p) :
    Nonempty (ValidDir p) := by
  rcases hTop with ⟨_, hDown, _, _⟩
  exact ⟨⟨Direction4.down, hDown⟩⟩

theorem nonempty_validDir_of_isBottomEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hBottom : IsBottomEdgeNoncorner p) :
    Nonempty (ValidDir p) := by
  rcases hBottom with ⟨hUp, _, _, _⟩
  exact ⟨⟨Direction4.up, hUp⟩⟩

theorem nonempty_validDir_of_isLeftEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hLeft : IsLeftEdgeNoncorner p) :
    Nonempty (ValidDir p) := by
  rcases hLeft with ⟨_, _, _, hRight⟩
  exact ⟨⟨Direction4.right, hRight⟩⟩

theorem nonempty_validDir_of_isRightEdgeNoncorner
    {h w : Nat}
    (p : Pixel h w)
    (hRight : IsRightEdgeNoncorner p) :
    Nonempty (ValidDir p) := by
  rcases hRight with ⟨_, _, hLeft, _⟩
  exact ⟨⟨Direction4.left, hLeft⟩⟩

end FastMLFE2.Theory.Theorems
