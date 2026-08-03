import IPNPCNS.Cone.Laws

/-!
# Population primitives and exact cone circuits

The ideal population primitive is equation (176), namely reflected conic rejection.
This module rewrites conic projection and intersection into circuits made from that
primitive, reflection, and closed cone sum.  It also states equation (210) under
explicit abstract control premises; no mechanism for detecting cone emptiness is
assumed or constructed here.
-/

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Equation (176): the ideal cone-level output of one generic population. -/
def populationPrimitive (P Q : ClosedCone H) : ClosedCone H :=
  coneReflection (coneRejection P Q)

/-- A primitive fed reflected inputs produces the unreflected rejection of the
original inputs.  This is equation (209) followed by reflection involution. -/
theorem populationPrimitive_reflected_inputs (P Q : ClosedCone H) :
    populationPrimitive (coneReflection P) (coneReflection Q) =
      coneRejection P Q := by
  unfold populationPrimitive
  rw [← coneReflection_rejection, coneReflection_involutive]

/-- Figure 9D: conic projection uses two rejection primitives and one standalone
reflection.  The inner primitive supplies the reflected inner rejection, so equation
(209) eliminates a second standalone reflection. -/
theorem coneProjection_eq_populationCircuit (P Q : ClosedCone H) :
    coneProjection P Q =
      populationPrimitive (coneReflection P) (populationPrimitive P Q) := by
  calc
    coneProjection P Q = coneRejection P (coneRejection P Q) :=
      doubleRejection P Q
    _ = populationPrimitive (coneReflection P)
          (coneReflection (coneRejection P Q)) :=
      (populationPrimitive_reflected_inputs P (coneRejection P Q)).symm
    _ = populationPrimitive (coneReflection P) (populationPrimitive P Q) := rfl

/-- Figure 9E: intersection uses three rejection primitives, one standalone
reflection, and closed cone sums. -/
theorem inf_eq_populationCircuit (P Q : ClosedCone H) :
    P ⊓ Q =
      populationPrimitive (coneReflection (coneSum P Q))
        (coneSum (populationPrimitive Q P) (populationPrimitive P Q)) := by
  calc
    P ⊓ Q = coneRejection (coneSum P Q) (rejectionSum P Q) :=
      inf_eq_sum_rejection P Q
    _ = populationPrimitive (coneReflection (coneSum P Q))
          (coneReflection (rejectionSum P Q)) :=
      (populationPrimitive_reflected_inputs (coneSum P Q) (rejectionSum P Q)).symm
    _ = populationPrimitive (coneReflection (coneSum P Q))
          (coneSum (populationPrimitive Q P) (populationPrimitive P Q)) := by
      apply congrArg (populationPrimitive (coneReflection (coneSum P Q)))
      calc
        coneReflection (rejectionSum P Q) =
            coneReflection
              (coneSum (coneRejection Q P) (coneRejection P Q)) := rfl
        _ = coneSum (coneReflection (coneRejection Q P))
              (coneReflection (coneRejection P Q)) :=
          (coneSum_reflection (coneRejection Q P) (coneRejection P Q)).symm
        _ = coneSum (populationPrimitive Q P) (populationPrimitive P Q) := rfl

/-- The control population is inactive exactly when the condition cone is empty.
This is a representational premise, not an implementation of an emptiness test. -/
def EmptinessControlPremise (C : ClosedCone H) (controlInactive : Prop) : Prop :=
  controlInactive ↔ C = ⊥

/-- An abstract strong inhibitory gate passes the signal when control is inactive
and blocks it to the zero cone when control is active. -/
def StrongBlockingPremise (controlInactive : Prop)
    (signal output : ClosedCone H) : Prop :=
  (controlInactive → output = signal) ∧
    (¬controlInactive → output = ⊥)

/-- The abstract cone-valued branch in equation (210). -/
noncomputable def emptyConeConditional
    (C signal : ClosedCone H) : ClosedCone H := by
  classical
  exact if C = ⊥ then signal else ⊥

/-- Equation (210).  The conclusion follows only from the explicit synchronized
emptiness-control premise and the explicit strong-blocking premise. -/
theorem controlledConditional210
    (C P Q output : ClosedCone H) (controlInactive : Prop)
    (hControl : EmptinessControlPremise C controlInactive)
    (hBlocking : StrongBlockingPremise controlInactive
      (populationPrimitive P Q) output) :
    output = emptyConeConditional C (populationPrimitive P Q) := by
  classical
  unfold emptyConeConditional
  by_cases hEmpty : C = ⊥
  · rw [if_pos hEmpty]
    exact hBlocking.1 (hControl.mpr hEmpty)
  · rw [if_neg hEmpty]
    exact hBlocking.2 fun hInactive => hEmpty (hControl.mp hInactive)

end

end IPNPCNS
