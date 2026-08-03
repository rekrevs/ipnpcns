import IPNPCNS.Subspace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Examples for finite-dimensional subspace algebra

The example below certifies the non-distributivity warning in equation (14).
-/

namespace IPNPCNS

noncomputable section

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def axis0 : Plane := EuclideanSpace.single 0 1
private def axis1 : Plane := EuclideanSpace.single 1 1
private def diagonal : Plane := axis0 + axis1

private def line0 : Submodule ℝ Plane := ℝ ∙ axis0
private def line1 : Submodule ℝ Plane := ℝ ∙ axis1
private def diagonalLine : Submodule ℝ Plane := ℝ ∙ diagonal

private theorem diagonal_ne_zero : diagonal ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : Plane => x 0) h
  norm_num [diagonal, axis0, axis1, PiLp.single_apply] at h0

private theorem diagonal_not_mem_line0 : diagonal ∉ line0 := by
  intro h
  rw [line0, Submodule.mem_span_singleton] at h
  obtain ⟨a, ha⟩ := h
  have h1 := congrArg (fun x : Plane => x 1) ha
  norm_num [diagonal, axis0, axis1, PiLp.single_apply] at h1

private theorem diagonal_not_mem_line1 : diagonal ∉ line1 := by
  intro h
  rw [line1, Submodule.mem_span_singleton] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congrArg (fun x : Plane => x 0) ha
  norm_num [diagonal, axis0, axis1, PiLp.single_apply] at h0

private theorem line0_inf_diagonalLine : line0 ⊓ diagonalLine = ⊥ := by
  exact disjoint_iff.mp
    (Submodule.disjoint_span_singleton_of_notMem diagonal_not_mem_line0)

private theorem line1_inf_diagonalLine : line1 ⊓ diagonalLine = ⊥ := by
  exact disjoint_iff.mp
    (Submodule.disjoint_span_singleton_of_notMem diagonal_not_mem_line1)

/-- Equation (14): sum does not distribute over intersection. -/
theorem subspace_sum_not_distributive :
    (line0 ⊔ line1) ⊓ diagonalLine ≠
      (line0 ⊓ diagonalLine) ⊔ (line1 ⊓ diagonalLine) := by
  intro h
  have hd0 : axis0 ∈ line0 := Submodule.mem_span_singleton_self axis0
  have hd1 : axis1 ∈ line1 := Submodule.mem_span_singleton_self axis1
  have hdSum : diagonal ∈ line0 ⊔ line1 := by
    exact Submodule.add_mem_sup hd0 hd1
  have hdDiag : diagonal ∈ diagonalLine := Submodule.mem_span_singleton_self diagonal
  have hdLeft : diagonal ∈ (line0 ⊔ line1) ⊓ diagonalLine := ⟨hdSum, hdDiag⟩
  have hdRight : diagonal ∈
      (line0 ⊓ diagonalLine) ⊔ (line1 ⊓ diagonalLine) := by
    rw [← h]
    exact hdLeft
  rw [line0_inf_diagonalLine, line1_inf_diagonalLine, bot_sup_eq] at hdRight
  exact diagonal_ne_zero hdRight

end

end IPNPCNS
