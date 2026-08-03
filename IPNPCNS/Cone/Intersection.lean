import IPNPCNS.Cone.DoubleRejection

/-!
# Intersection from conic rejection and sum

This module formalizes equations (109) and (155)–(157).
-/

open Set

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Pointwise sums used to generate the closed Minkowski sum in equation (72). -/
def sumSet (A B : ClosedCone H) : Set H :=
  {z | ∃ x ∈ A, ∃ y ∈ B, x + y = z}

/-- Equation (72): the closed conic hull of pointwise sums. -/
def coneSum (A B : ClosedCone H) : ClosedCone H :=
  conicHull (sumSet A B)

theorem add_mem_coneSum (A B : ClosedCone H) {x y : H}
    (hx : x ∈ A) (hy : y ∈ B) : x + y ∈ coneSum A B :=
  subset_conicHull (sumSet A B) ⟨x, hx, y, hy, rfl⟩

theorem left_le_coneSum (A B : ClosedCone H) : A ≤ coneSum A B := by
  intro x hx
  simpa using add_mem_coneSum A B hx B.zero_mem

theorem right_le_coneSum (A B : ClosedCone H) : B ≤ coneSum A B := by
  intro y hy
  simpa using add_mem_coneSum A B A.zero_mem hy

theorem coneSum_le {A B D : ClosedCone H} (hA : A ≤ D) (hB : B ≤ D) :
    coneSum A B ≤ D := by
  apply conicHull_le
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact D.add_mem (hA hx) (hB hy)

theorem conicHull_coe (C : ClosedCone H) : conicHull (C : Set H) = C := by
  apply le_antisymm
  · exact conicHull_le fun _ => id
  · exact subset_conicHull (C : Set H)

variable [CompleteSpace H]

theorem metricProjection_eq_self {C : ClosedCone H} {x : H} (hx : x ∈ C) :
    metricProjection C x = x := by
  apply metricProjection_eq_of_mem_of_inner_le_zero C x x hx
  simp

theorem mem_polar_coneSum_iff {A B : ClosedCone H} {z : H} :
    z ∈ polar (coneSum A B) ↔ z ∈ polar A ∧ z ∈ polar B := by
  constructor
  · intro hz
    exact ⟨polar_antitone (left_le_coneSum A B) hz,
      polar_antitone (right_le_coneSum A B) hz⟩
  · rintro ⟨hzA, hzB⟩
    let Z : ClosedCone H := conicHull ({z} : Set H)
    have hzZ : z ∈ Z := subset_conicHull ({z} : Set H) (by simp)
    have hZA : Z ≤ polar A := by
      apply conicHull_le
      simpa using hzA
    have hZB : Z ≤ polar B := by
      apply conicHull_le
      simpa using hzB
    have hA : A ≤ polar Z := by
      have h := polar_antitone hZA
      simpa only [polar_polar] using h
    have hB : B ≤ polar Z := by
      have h := polar_antitone hZB
      simpa only [polar_polar] using h
    have hsum : coneSum A B ≤ polar Z := coneSum_le hA hB
    exact polar_antitone hsum (subset_polar_polar Z hzZ)

/-- Equation (110): the sum of the two directional rejection cones. -/
def rejectionSum (A B : ClosedCone H) : ClosedCone H :=
  coneSum (coneRejection B A) (coneRejection A B)

theorem inf_le_polar_rejectionSum (A B : ClosedCone H) :
    A ⊓ B ≤ polar (rejectionSum A B) := by
  intro x hx
  change x ∈ polar (coneSum (coneRejection B A) (coneRejection A B))
  rw [mem_polar_coneSum_iff]
  constructor
  · exact polar_antitone (coneRejection_le_polar B A)
      (subset_polar_polar A hx.1)
  · exact polar_antitone (coneRejection_le_polar A B)
      (subset_polar_polar B hx.2)

omit [CompleteSpace H] in
private theorem crossTerm_le (u₀ v₀ vᵤ uᵥ rᵤ rᵥ : H)
    (huv : inner ℝ u₀ uᵥ ≤ 0) (hvu : inner ℝ v₀ vᵤ ≤ 0)
    (hrel : u₀ - v₀ = -(vᵤ - uᵥ) - (rᵤ - rᵥ)) :
    inner ℝ u₀ vᵤ + inner ℝ v₀ uᵥ ≤
      (1 / 2 : ℝ) * (inner ℝ rᵤ rᵤ + inner ℝ rᵥ rᵥ) := by
  have hcross :
      inner ℝ u₀ vᵤ + inner ℝ v₀ uᵥ ≤
        inner ℝ (u₀ - v₀) (vᵤ - uᵥ) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    nlinarith
  have hsquare :=
    real_inner_self_nonneg
      (x := (vᵤ - uᵥ) + (1 / 2 : ℝ) • (rᵤ - rᵥ))
  have hcomplete :
      -inner ℝ (vᵤ - uᵥ) (vᵤ - uᵥ) -
          inner ℝ (rᵤ - rᵥ) (vᵤ - uᵥ) ≤
        (1 / 4 : ℝ) * inner ℝ (rᵤ - rᵥ) (rᵤ - rᵥ) := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      inner_smul_right] at hsquare
    have hcomm :
        inner ℝ (vᵤ - uᵥ) (rᵤ - rᵥ) =
          inner ℝ (rᵤ - rᵥ) (vᵤ - uᵥ) := real_inner_comm _ _
    nlinarith
  have hdiffSquare :=
    real_inner_self_nonneg (x := rᵤ + rᵥ)
  have hdiff :
      inner ℝ (rᵤ - rᵥ) (rᵤ - rᵥ) ≤
        2 * (inner ℝ rᵤ rᵤ + inner ℝ rᵥ rᵥ) := by
    simp only [inner_add_left, inner_add_right] at hdiffSquare
    simp only [inner_sub_left, inner_sub_right]
    have hcomm : inner ℝ rᵤ rᵥ = inner ℝ rᵥ rᵤ := real_inner_comm _ _
    nlinarith
  have hrewrite :
      inner ℝ (u₀ - v₀) (vᵤ - uᵥ) =
        -inner ℝ (vᵤ - uᵥ) (vᵤ - uᵥ) -
          inner ℝ (rᵤ - rᵥ) (vᵤ - uᵥ) := by
    rw [hrel, inner_sub_left, inner_neg_left]
  rw [hrewrite] at hcross
  nlinarith

set_option maxHeartbeats 800000 in
/-- Equations (114) and (139): on the polar of the rejection sum, projection onto
`A`, `B`, and their intersection agrees. -/
theorem metricProjection_eq_inf_of_mem_polar_rejectionSum
    (A B : ClosedCone H) (q : H) (hq : q ∈ polar (rejectionSum A B)) :
    metricProjection A q = metricProjection (A ⊓ B) q ∧
      metricProjection B q = metricProjection (A ⊓ B) q := by
  let u := metricProjection A q
  let uPolar := metricProjection (polar A) q
  let v := metricProjection B q
  let vPolar := metricProjection (polar B) q
  let vFromU := metricProjection B u
  let rU := metricProjection (polar B) u
  let uFromV := metricProjection A v
  let rV := metricProjection (polar A) v

  have huA : u ∈ A := by
    simpa [u] using metricProjection_mem A q
  have huPolarA : uPolar ∈ polar A := by
    simpa [uPolar] using metricProjection_mem (polar A) q
  have hvB : v ∈ B := by
    simpa [v] using metricProjection_mem B q
  have hvPolarB : vPolar ∈ polar B := by
    simpa [vPolar] using metricProjection_mem (polar B) q
  have hvFromUB : vFromU ∈ B := by
    simpa [vFromU] using metricProjection_mem B u
  have hrUPolarB : rU ∈ polar B := by
    simpa [rU] using metricProjection_mem (polar B) u
  have huFromVA : uFromV ∈ A := by
    simpa [uFromV] using metricProjection_mem A v
  have hrVPolarA : rV ∈ polar A := by
    simpa [rV] using metricProjection_mem (polar A) v

  have hqU : q = u + uPolar := by
    simpa [u, uPolar] using moreau_add A q
  have hqV : q = v + vPolar := by
    simpa [v, vPolar] using moreau_add B q
  have hU : u = vFromU + rU := by
    simpa [vFromU, rU] using moreau_add B u
  have hV : v = uFromV + rV := by
    simpa [uFromV, rV] using moreau_add A v
  have horthU : inner ℝ u uPolar = 0 := by
    simpa [u, uPolar] using moreau_inner A q
  have horthV : inner ℝ v vPolar = 0 := by
    simpa [v, vPolar] using moreau_inner B q
  have horthRU : inner ℝ vFromU rU = 0 := by
    simpa [vFromU, rU] using moreau_inner B u
  have horthRV : inner ℝ uFromV rV = 0 := by
    simpa [uFromV, rV] using moreau_inner A v

  have hrURejection : rU ∈ coneRejection A B := by
    simpa [rU] using metricProjection_polar_mem_coneRejection A B huA
  have hrVRejection : rV ∈ coneRejection B A := by
    simpa [rV] using metricProjection_polar_mem_coneRejection B A hvB
  have hqSum : q ∈ polar
      (coneSum (coneRejection B A) (coneRejection A B)) := by
    simpa [rejectionSum] using hq
  have hqRU : inner ℝ q rU ≤ 0 := by
    have hqRight : q ∈ polar (coneRejection A B) :=
      (mem_polar_coneSum_iff.mp hqSum).2
    exact (mem_polar.mp hqRight) rU hrURejection
  have hqRV : inner ℝ q rV ≤ 0 := by
    have hqLeft : q ∈ polar (coneRejection B A) :=
      (mem_polar_coneSum_iff.mp hqSum).1
    exact (mem_polar.mp hqLeft) rV hrVRejection

  have huPolarUFromV : inner ℝ uPolar uFromV ≤ 0 :=
    (mem_polar.mp huPolarA) uFromV huFromVA
  have hvPolarVFromU : inner ℝ vPolar vFromU ≤ 0 :=
    (mem_polar.mp hvPolarB) vFromU hvFromUB
  have huPolarEq : uPolar = q - u := by
    rw [hqU]
    abel
  have hvPolarEq : vPolar = q - v := by
    rw [hqV]
    abel
  have hrUEq : rU = u - vFromU := by
    rw [hU]
    abel
  have hrVEq : rV = v - uFromV := by
    rw [hV]
    abel
  have hrelation :
      uPolar - vPolar = -(vFromU - uFromV) - (rU - rV) := by
    rw [huPolarEq, hvPolarEq, hrUEq, hrVEq]
    abel
  have hcross := crossTerm_le uPolar vPolar vFromU uFromV rU rV
    huPolarUFromV hvPolarVFromU hrelation

  have huPolarU : inner ℝ uPolar u = 0 := by
    simpa [real_inner_comm] using horthU
  have hvPolarV : inner ℝ vPolar v = 0 := by
    simpa [real_inner_comm] using horthV
  have huPolarRU : inner ℝ uPolar rU = -inner ℝ uPolar vFromU := by
    rw [hU, inner_add_right] at huPolarU
    linarith
  have hvPolarRV : inner ℝ vPolar rV = -inner ℝ vPolar uFromV := by
    rw [hV, inner_add_right] at hvPolarV
    linarith
  have huRU : inner ℝ u rU = inner ℝ rU rU := by
    rw [hU, inner_add_left, horthRU, zero_add]
  have hvRV : inner ℝ v rV = inner ℝ rV rV := by
    rw [hV, inner_add_left, horthRV, zero_add]
  have hqRUEq :
      inner ℝ q rU = inner ℝ rU rU - inner ℝ uPolar vFromU := by
    rw [hqU, inner_add_left, huRU, huPolarRU]
    simp only [sub_eq_add_neg]
  have hqRVEq :
      inner ℝ q rV = inner ℝ rV rV - inner ℝ vPolar uFromV := by
    rw [hqV, inner_add_left, hvRV, hvPolarRV]
    simp only [sub_eq_add_neg]
  have hlower :
      (1 / 2 : ℝ) * (inner ℝ rU rU + inner ℝ rV rV) ≤
        inner ℝ q rU + inner ℝ q rV := by
    rw [hqRUEq, hqRVEq]
    nlinarith
  have hrUNonneg : 0 ≤ inner ℝ rU rU := real_inner_self_nonneg
  have hrVNonneg : 0 ≤ inner ℝ rV rV := real_inner_self_nonneg
  have hqUpper : inner ℝ q rU + inner ℝ q rV ≤ 0 := by
    linarith only [hqRU, hqRV]
  have hselfSum : inner ℝ rU rU + inner ℝ rV rV = 0 := by
    nlinarith only [hlower, hqUpper, hrUNonneg, hrVNonneg]
  have hrUSelf : inner ℝ rU rU = 0 := by
    nlinarith only [hselfSum, hrUNonneg, hrVNonneg]
  have hrVSelf : inner ℝ rV rV = 0 := by
    nlinarith only [hselfSum, hrUNonneg, hrVNonneg]
  have hrUZero : rU = 0 := by
    rw [real_inner_self_eq_norm_sq] at hrUSelf
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hrUSelf)
  have hrVZero : rV = 0 := by
    rw [real_inner_self_eq_norm_sq] at hrVSelf
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hrVSelf)

  have huEq : u = vFromU := by simpa [hrUZero] using hU
  have hvEq : v = uFromV := by simpa [hrVZero] using hV
  have huB : u ∈ B := by
    rw [huEq]
    exact hvFromUB
  have hvA : v ∈ A := by
    rw [hvEq]
    exact huFromVA
  have huInf : u ∈ A ⊓ B := ⟨huA, huB⟩
  have hvInf : v ∈ A ⊓ B := ⟨hvA, hvB⟩
  have huPolarInf : uPolar ∈ polar (A ⊓ B) :=
    polar_antitone inf_le_left huPolarA
  have hvPolarInf : vPolar ∈ polar (A ⊓ B) :=
    polar_antitone inf_le_right hvPolarB
  have hprojU :=
    metricProjection_eq_of_mem_of_mem_polar_inner_eq_zero
      (A ⊓ B) q u uPolar huInf huPolarInf horthU hqU
  have hprojV :=
    metricProjection_eq_of_mem_of_mem_polar_inner_eq_zero
      (A ⊓ B) q v vPolar hvInf hvPolarInf horthV hqV
  exact ⟨by simpa [u] using hprojU.symm, by simpa [v] using hprojV.symm⟩

/-- Equation (115): the residual from the common projection is polar to the closed
sum of the source cones. -/
theorem sub_metricProjection_inf_mem_polar_coneSum
    (A B : ClosedCone H) (q : H) (hq : q ∈ polar (rejectionSum A B)) :
    q - metricProjection (A ⊓ B) q ∈ polar (coneSum A B) := by
  rcases metricProjection_eq_inf_of_mem_polar_rejectionSum A B q hq with
    ⟨hA, hB⟩
  rw [mem_polar_coneSum_iff]
  constructor
  · rw [← hA]
    exact sub_metricProjection_mem_polar A q
  · rw [← hB]
    exact sub_metricProjection_mem_polar B q

/-- Equations (142)–(149): projecting any point of `A + B` onto the polar of
the rejection sum gives its projection onto `A ∩ B`. -/
theorem metricProjection_polar_rejectionSum_eq_inf
    (A B : ClosedCone H) (x : H) (hx : x ∈ coneSum A B) :
    metricProjection (polar (rejectionSum A B)) x =
      metricProjection (A ⊓ B) x := by
  let q := metricProjection (polar (rejectionSum A B)) x
  let p := metricProjection (polar (polar (rejectionSum A B))) x
  let g := metricProjection (A ⊓ B) q
  let t := q - g

  have hqK : q ∈ polar (rejectionSum A B) := by
    simpa [q] using metricProjection_mem (polar (rejectionSum A B)) x
  have hpPolarK : p ∈ polar (polar (rejectionSum A B)) := by
    simpa [p] using
      metricProjection_mem (polar (polar (rejectionSum A B))) x
  have hxSplit : x = q + p := by
    simpa [q, p] using moreau_add (polar (rejectionSum A B)) x
  have horthQP : inner ℝ q p = 0 := by
    simpa [q, p] using moreau_inner (polar (rejectionSum A B)) x

  have hgInf : g ∈ A ⊓ B := by
    simpa [g] using metricProjection_mem (A ⊓ B) q
  have hgK : g ∈ polar (rejectionSum A B) :=
    inf_le_polar_rejectionSum A B hgInf
  have htSum : t ∈ polar (coneSum A B) := by
    simpa [g, t] using
      sub_metricProjection_inf_mem_polar_coneSum A B q hqK
  have hpg : inner ℝ p g ≤ 0 :=
    (mem_polar.mp hpPolarK) g hgK
  have hpq : inner ℝ p q = 0 := by
    simpa [real_inner_comm] using horthQP
  have hpt : 0 ≤ inner ℝ p t := by
    have heq : inner ℝ p t = inner ℝ p q - inner ℝ p g := by
      simp only [t, inner_sub_right]
    rw [heq, hpq, zero_sub]
    linarith
  have htp : 0 ≤ inner ℝ t p := by
    simpa [real_inner_comm] using hpt
  have htx : inner ℝ t x ≤ 0 :=
    (mem_polar.mp htSum) x hx
  have hgt : inner ℝ g t = 0 := by
    simpa [g, t] using inner_metricProjection_sub_eq_zero (A ⊓ B) q
  have htg : inner ℝ t g = 0 := by
    simpa [real_inner_comm] using hgt
  have hxExpanded : x = g + t + p := by
    rw [hxSplit]
    dsimp only [t]
    abel
  have htxEq : inner ℝ t x = inner ℝ t t + inner ℝ t p := by
    rw [hxExpanded, inner_add_right, inner_add_right, htg, zero_add]
  have httNonneg : 0 ≤ inner ℝ t t := real_inner_self_nonneg
  have httZero : inner ℝ t t = 0 := by
    nlinarith only [htx, htxEq, htp, httNonneg]
  have htZero : t = 0 := by
    rw [real_inner_self_eq_norm_sq] at httZero
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp httZero)
  have hqg : q = g := by
    apply sub_eq_zero.mp
    simpa [t] using htZero
  have hqInf : q ∈ A ⊓ B := by
    rw [hqg]
    exact hgInf
  have hpInfPolar : p ∈ polar (A ⊓ B) :=
    polar_antitone (inf_le_polar_rejectionSum A B) hpPolarK
  have hproj :=
    metricProjection_eq_of_mem_of_mem_polar_inner_eq_zero
      (A ⊓ B) x q p hqInf hpInfPolar horthQP hxSplit
  change q = metricProjection (A ⊓ B) x
  exact hproj.symm

/-- Equations (150)–(154): any source cone between the intersection and the closed
sum projects onto exactly the intersection. -/
theorem coneProjection_polar_rejectionSum_eq_inf
    (A B S : ClosedCone H) (hInfS : A ⊓ B ≤ S) (hSSum : S ≤ coneSum A B) :
    coneProjection S (polar (rejectionSum A B)) = A ⊓ B := by
  apply le_antisymm
  · change conicHull (projectedSet S (polar (rejectionSum A B))) ≤ A ⊓ B
    apply conicHull_le
    rintro y ⟨x, hxS, rfl⟩
    rw [metricProjection_polar_rejectionSum_eq_inf A B x (hSSum hxS)]
    exact metricProjection_mem (A ⊓ B) x
  · intro x hxInf
    have hxS : x ∈ S := hInfS hxInf
    have hxK : x ∈ polar (rejectionSum A B) :=
      inf_le_polar_rejectionSum A B hxInf
    have hgen :=
      metricProjection_mem_coneProjection S (polar (rejectionSum A B)) hxS
    rw [metricProjection_eq_self hxK] at hgen
    exact hgen

/-- Equation (155). -/
theorem inf_eq_left_rejection (A B : ClosedCone H) :
    A ⊓ B = coneRejection A (rejectionSum A B) := by
  symm
  change coneProjection A (polar (rejectionSum A B)) = A ⊓ B
  exact coneProjection_polar_rejectionSum_eq_inf A B A inf_le_left
    (left_le_coneSum A B)

/-- Equation (156). -/
theorem inf_eq_right_rejection (A B : ClosedCone H) :
    A ⊓ B = coneRejection B (rejectionSum A B) := by
  symm
  change coneProjection B (polar (rejectionSum A B)) = A ⊓ B
  exact coneProjection_polar_rejectionSum_eq_inf A B B inf_le_right
    (right_le_coneSum A B)

/-- Equation (157). -/
theorem inf_eq_sum_rejection (A B : ClosedCone H) :
    A ⊓ B = coneRejection (coneSum A B) (rejectionSum A B) := by
  symm
  change coneProjection (coneSum A B) (polar (rejectionSum A B)) = A ⊓ B
  exact coneProjection_polar_rejectionSum_eq_inf A B (coneSum A B)
    (inf_le_left.trans (left_le_coneSum A B)) le_rfl

/-- Equation (109), collecting all three rejection-only intersection formulas. -/
theorem intersectionByRejections (A B : ClosedCone H) :
    A ⊓ B = coneRejection A (rejectionSum A B) ∧
      A ⊓ B = coneRejection B (rejectionSum A B) ∧
      A ⊓ B = coneRejection (coneSum A B) (rejectionSum A B) :=
  ⟨inf_eq_left_rejection A B, inf_eq_right_rejection A B,
    inf_eq_sum_rejection A B⟩

end

end IPNPCNS
