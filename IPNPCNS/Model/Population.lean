import IPNPCNS.Cone.Operations

/-!
# Conditional population-level realization

The paper's support masks, learned matrix, message family, and active face determine a
selected population map. This module packages exactly the assumptions needed for
equations (204), (206), (207), and (208), without claiming that biological systems
satisfy them.
-/

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- One face/support region of the population realization in Section 5.3. -/
structure PopulationRegion (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  source : ClosedCone H
  target : ClosedCone H
  messageModel : Set H
  region : Set H
  /-- The face-span projector selected in this region. -/
  faceProjection : H → H
  /-- The support-selected end-to-end population map `T` from equation (201). -/
  populationMap : H → H
  /-- Equation (199), isolated from the learning assumption. -/
  projection_eq_face :
    ∀ u ∈ region, metricProjection target u = faceProjection u

/-- Membership in the domain on which equation (204) makes a claim. -/
def PopulationRegion.Relevant (R : PopulationRegion H) (u : H) : Prop :=
  u ∈ R.source ∧ u ∈ R.messageModel ∧ u ∈ R.region

/-- Equation (204), as an explicit assumption on the represented message family. -/
def PopulationRegion.Approximation204
    (R : PopulationRegion H) (ε : ℝ) : Prop :=
  ∀ u, R.Relevant u →
    ‖R.populationMap u - R.faceProjection u‖ ≤ ε * ‖u‖

/-- Equation (206): (204) and the face identity (199) imply approximation of the
pointwise cone projection. -/
theorem PopulationRegion.projection_error206
    (R : PopulationRegion H) {ε : ℝ}
    (h204 : R.Approximation204 ε) {u : H} (hu : R.Relevant u) :
    ‖R.populationMap u - metricProjection R.target u‖ ≤ ε * ‖u‖ := by
  rw [R.projection_eq_face u hu.2.2]
  exact h204 u hu

/-- Equation (207): the population residual has the same error as the reconstructed
projection. -/
theorem PopulationRegion.residual_error207
    (R : PopulationRegion H) {ε : ℝ}
    (h204 : R.Approximation204 ε) {u : H} (hu : R.Relevant u) :
    ‖(u - R.populationMap u) - (u - metricProjection R.target u)‖ ≤
      ε * ‖u‖ := by
  have h := R.projection_error206 h204 hu
  have heq :
      (u - R.populationMap u) - (u - metricProjection R.target u) =
        -(R.populationMap u - metricProjection R.target u) := by
    abel
  rw [heq, norm_neg]
  exact h

/-- Equation (208): exact agreement on the complete source cone gives exact equality
of the reconstructed and residual conic hulls. -/
theorem exact_population_hulls
    (P Q : ClosedCone H) (T : H → H)
    (hExact : ∀ u ∈ P, T u = metricProjection Q u) :
    conicHull (T '' (P : Set H)) = coneProjection P Q ∧
      conicHull ((fun u => u - T u) '' (P : Set H)) = coneRejection P Q := by
  constructor
  · change conicHull (T '' (P : Set H)) =
      conicHull (projectedSet P Q)
    congr 1
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, (hExact u hu).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, hExact u hu⟩
  · rw [coneRejection_eq_residualHull]
    congr 1
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, congrArg (fun z => u - z) (hExact u hu).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, congrArg (fun z => u - z) (hExact u hu)⟩

/-- The ideal `ε = 0` case of (204), when every source message is covered by the
message model and a face region, implies equation (208). -/
theorem PopulationRegion.exact_hulls_of_zero
    (R : PopulationRegion H)
    (hcover : ∀ u ∈ R.source, u ∈ R.messageModel ∧ u ∈ R.region)
    (h204 : R.Approximation204 0) :
    conicHull (R.populationMap '' (R.source : Set H)) =
        coneProjection R.source R.target ∧
      conicHull ((fun u => u - R.populationMap u) '' (R.source : Set H)) =
        coneRejection R.source R.target := by
  apply exact_population_hulls R.source R.target R.populationMap
  intro u hu
  have hrel : R.Relevant u := ⟨hu, (hcover u hu).1, (hcover u hu).2⟩
  have hnorm : ‖R.populationMap u - R.faceProjection u‖ = 0 := by
    apply le_antisymm
    · simpa using h204 u hrel
    · exact norm_nonneg _
  have hmapFace : R.populationMap u = R.faceProjection u :=
    sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  exact hmapFace.trans (R.projection_eq_face u hrel.2.2).symm

end

end IPNPCNS
