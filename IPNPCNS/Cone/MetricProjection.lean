import IPNPCNS.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Metric projection onto a closed convex cone

The projection is noncomputable: it selects the unique closest point whose existence is
provided by the Hilbert projection theorem.
-/

open Set

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem exists_metricProjection (C : ClosedCone H) (x : H) :
    ∃ y ∈ C, ‖x - y‖ = ⨅ z : C, ‖x - z‖ :=
  exists_norm_eq_iInf_of_complete_convex C.nonempty C.isClosed.isComplete C.convex x

/-- Equation (65): metric projection onto a closed convex cone. -/
def metricProjection (C : ClosedCone H) (x : H) : H :=
  Classical.choose (exists_metricProjection C x)

theorem metricProjection_mem (C : ClosedCone H) (x : H) :
    metricProjection C x ∈ C :=
  (Classical.choose_spec (exists_metricProjection C x)).1

theorem metricProjection_minimal (C : ClosedCone H) (x : H) :
    ‖x - metricProjection C x‖ = ⨅ z : C, ‖x - z‖ :=
  (Classical.choose_spec (exists_metricProjection C x)).2

/-- Equation (69): the variational characterization of the chosen projection. -/
theorem metricProjection_inner_le_zero (C : ClosedCone H) (x : H) :
    ∀ y ∈ C, inner ℝ (x - metricProjection C x) (y - metricProjection C x) ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero C.convex (metricProjection_mem C x)).mp
    (metricProjection_minimal C x)

end

end IPNPCNS
