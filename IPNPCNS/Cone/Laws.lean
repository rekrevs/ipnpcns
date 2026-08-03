import IPNPCNS.Cone.Intersection

/-!
# Exact laws for the closed-cone algebra

This module completes equations (93)--(97) and formalizes reflection, including
equation (209).  Reflection is defined as pullback along the continuous linear
equivalence `x \mapsto -x`; consequently it preserves closedness by construction.
-/

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Equation (93): conic projection is contained in its target cone. -/
theorem coneProjection_subset_right (A B : ClosedCone H) :
    coneProjection A B ≤ B :=
  coneProjection_le_right A B

/-- Equation (94): polarity reverses and reflects cone inclusion. -/
theorem le_iff_polar_ge {A B : ClosedCone H} :
    A ≤ B ↔ polar B ≤ polar A := by
  constructor
  · exact polar_antitone
  · intro h
    have hp := polar_antitone h
    simpa only [polar_polar] using hp

/-- Equation (95), in the orientation printed in the paper. -/
theorem eq_polar_polar (A : ClosedCone H) : A = polar (polar A) :=
  (polar_polar A).symm

/-- Projecting a source point onto the conic projection has the same result as
projecting it onto the original target. -/
theorem metricProjection_coneProjection_eq (A B : ClosedCone H) (x : H)
    (hx : x ∈ A) :
    metricProjection (coneProjection A B) x = metricProjection B x := by
  apply metricProjection_eq_of_mem_of_inner_le_zero
  · exact metricProjection_mem_coneProjection A B hx
  · intro z hz
    exact metricProjection_inner_le_zero B x z
      (coneProjection_le_right A B hz)

/-- Equation (96): conic projection absorbs repetition with the same source. -/
theorem coneProjection_absorb (A B : ClosedCone H) :
    coneProjection A (coneProjection A B) = coneProjection A B := by
  apply le_antisymm
  · exact coneProjection_le_right A (coneProjection A B)
  · change conicHull (projectedSet A B) ≤
      coneProjection A (coneProjection A B)
    apply conicHull_le
    rintro y ⟨x, hx, rfl⟩
    have hgen :=
      metricProjection_mem_coneProjection A (coneProjection A B) hx
    rw [metricProjection_coneProjection_eq A B x hx] at hgen
    exact hgen

/-- Equation (97): intersection is the polar of the closed sum of the two
polar cones. -/
theorem inf_eq_polar_coneSum_polar (A B : ClosedCone H) :
    A ⊓ B = polar (coneSum (polar A) (polar B)) := by
  ext z
  change (z ∈ A ∧ z ∈ B) ↔ z ∈ polar (coneSum (polar A) (polar B))
  rw [mem_polar_coneSum_iff]
  constructor
  · rintro ⟨hzA, hzB⟩
    constructor
    · simpa only [polar_polar] using hzA
    · simpa only [polar_polar] using hzB
  · rintro ⟨hzA, hzB⟩
    constructor
    · simpa only [polar_polar] using hzA
    · simpa only [polar_polar] using hzB

/-- Equation (80): reflection of a closed cone through the origin. -/
def coneReflection (C : ClosedCone H) : ClosedCone H :=
  C.comap (ContinuousLinearEquiv.neg ℝ).toContinuousLinearMap

omit [CompleteSpace H] in
@[simp]
theorem mem_coneReflection {C : ClosedCone H} {x : H} :
    x ∈ coneReflection C ↔ -x ∈ C := by
  simp [coneReflection]

omit [CompleteSpace H] in
/-- Reflection is monotone for cone inclusion. -/
theorem coneReflection_mono {A B : ClosedCone H} (h : A ≤ B) :
    coneReflection A ≤ coneReflection B := by
  intro x hx
  rw [mem_coneReflection] at hx ⊢
  exact h hx

omit [CompleteSpace H] in
@[simp]
theorem coneReflection_involutive (C : ClosedCone H) :
    coneReflection (coneReflection C) = C := by
  ext x
  simp

omit [CompleteSpace H] in
@[simp]
theorem coneReflection_bot :
    coneReflection (⊥ : ClosedCone H) = ⊥ := by
  ext x
  simp

/-- The paper's non-positive polar commutes with reflection.  In particular, the
sign convention is unchanged by equation (80). -/
theorem polar_coneReflection (C : ClosedCone H) :
    polar (coneReflection C) = coneReflection (polar C) := by
  ext z
  rw [mem_polar, mem_coneReflection, mem_polar]
  constructor
  · intro hz y hy
    have h := hz (-y) (by simp [hy])
    simpa only [inner_neg_left, inner_neg_right] using h
  · intro hz y hy
    have h := hz (-y) (by simpa using hy)
    simpa only [inner_neg_left, inner_neg_right, neg_neg] using h

/-- Metric projection is equivariant under simultaneous reflection of the point and
the target cone. -/
theorem metricProjection_coneReflection_neg (C : ClosedCone H) (x : H) :
    metricProjection (coneReflection C) (-x) = -metricProjection C x := by
  apply metricProjection_eq_of_mem_of_inner_le_zero
  · rw [mem_coneReflection]
    simpa using metricProjection_mem C x
  · intro z hz
    rw [mem_coneReflection] at hz
    have h := metricProjection_inner_le_zero C x (-z) hz
    rw [show -x - -metricProjection C x =
          -(x - metricProjection C x) by abel,
      show z - -metricProjection C x =
          -(-z - metricProjection C x) by abel,
      inner_neg_left, inner_neg_right, neg_neg]
    exact h

private theorem coneProjection_reflection_le (A B : ClosedCone H) :
    coneProjection (coneReflection A) (coneReflection B) ≤
      coneReflection (coneProjection A B) := by
  change conicHull (projectedSet (coneReflection A) (coneReflection B)) ≤
    coneReflection (coneProjection A B)
  apply conicHull_le
  rintro y ⟨x, hx, rfl⟩
  have hxA : -x ∈ A := mem_coneReflection.mp hx
  apply mem_coneReflection.mpr
  have hgen := metricProjection_mem_coneProjection A B hxA
  have hproj :
      metricProjection (coneReflection B) x =
        -metricProjection B (-x) := by
    simpa using metricProjection_coneReflection_neg B (-x)
  rw [hproj, neg_neg]
  exact hgen

/-- Conic projection commutes with simultaneous reflection of source and target. -/
theorem coneProjection_reflection (A B : ClosedCone H) :
    coneProjection (coneReflection A) (coneReflection B) =
      coneReflection (coneProjection A B) := by
  apply le_antisymm
  · exact coneProjection_reflection_le A B
  · have h := coneProjection_reflection_le (coneReflection A) (coneReflection B)
    have hreflected := coneReflection_mono h
    simpa only [coneReflection_involutive] using hreflected

omit [CompleteSpace H] in
private theorem coneSum_reflection_le (A B : ClosedCone H) :
    coneSum (coneReflection A) (coneReflection B) ≤
      coneReflection (coneSum A B) := by
  apply coneSum_le
  · intro x hx
    rw [mem_coneReflection] at hx ⊢
    exact left_le_coneSum A B hx
  · intro x hx
    rw [mem_coneReflection] at hx ⊢
    exact right_le_coneSum A B hx

omit [CompleteSpace H] in
/-- Closed cone sum commutes with simultaneous reflection. -/
theorem coneSum_reflection (A B : ClosedCone H) :
    coneSum (coneReflection A) (coneReflection B) =
      coneReflection (coneSum A B) := by
  apply le_antisymm
  · exact coneSum_reflection_le A B
  · have h := coneSum_reflection_le (coneReflection A) (coneReflection B)
    have hreflected := coneReflection_mono h
    simpa only [coneReflection_involutive] using hreflected

/-- Equation (209): reflection commutes with conic rejection when both inputs are
reflected. -/
theorem coneReflection_rejection (Y X : ClosedCone H) :
    coneReflection (coneRejection Y X) =
      coneRejection (coneReflection Y) (coneReflection X) := by
  calc
    coneReflection (coneRejection Y X) =
        coneProjection (coneReflection Y) (coneReflection (polar X)) := by
          simpa only [coneRejection] using
            (coneProjection_reflection Y (polar X)).symm
    _ = coneProjection (coneReflection Y) (polar (coneReflection X)) := by
          rw [polar_coneReflection]
    _ = coneRejection (coneReflection Y) (coneReflection X) := rfl

end

end IPNPCNS
