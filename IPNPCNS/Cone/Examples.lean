import IPNPCNS.Cone.DoubleRejection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-dimensional regression examples
-/

namespace IPNPCNS

noncomputable section

/-- The headline identity specializes without extra assumptions to two-dimensional
Euclidean space. -/
example (A B : ClosedCone (EuclideanSpace ℝ (Fin 2))) :
    coneProjection A B = coneRejection A (coneRejection A B) :=
  doubleRejection A B

end

end IPNPCNS
