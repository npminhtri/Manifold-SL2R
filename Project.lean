import Project.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.LocalHomeomorph
import Mathlib.Init.Align
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Analysis.InnerProductSpace.PiL2


def hello_world := hello ++ " world"

universe u
open TopologicalSpace
noncomputable section

/- Definition of SL(2,ℝ ) and charts by hand -/
def Special_lineargroup_order_2 [Zero (Fin 4)] : Type :=
   { x : EuclideanSpace ℝ (Fin 4) // (x 1)*(x 4) - (x 2)*(x 3) =1 }


/- Definition of four charts that covers SL(2,ℝ )-/
def Firstchart  [Zero (Fin 4)] : Type :=
  { x : EuclideanSpace ℝ (Fin 4) // (x 1)*(x 4) - (x 2)*(x 3) =1 ∧ (x 1) ≠ 0}
def Secondchart  [Zero (Fin 4)] : Type :=
  { x : EuclideanSpace ℝ (Fin 4) // (x 1)*(x 4) - (x 2)*(x 3) =1 ∧ (x 2) ≠ 0}
def Thirdchart  [Zero (Fin 4)] : Type :=
  { x : EuclideanSpace ℝ (Fin 4) // (x 1)*(x 4) - (x 2)*(x 3) =1 ∧ (x 3) ≠ 0}
def Fourthchart  [Zero (Fin 4)] : Type :=
  { x : EuclideanSpace ℝ (Fin 4) // (x 1)*(x 4) - (x 2)*(x 3) =1 ∧ (x 4) ≠ 0}
/- This is use to define a topological structure on SL(2,ℝ)
-/
section

instance [Zero (Fin 4)] : TopologicalSpace (Special_lineargroup_order_2) := instTopologicalSpaceSubtype
instance [Zero (Fin 4)]: TopologicalSpace (Firstchart) :=
  instTopologicalSpaceSubtype
instance [Zero (Fin 4)]: TopologicalSpace (Secondchart) := by apply
  instTopologicalSpaceSubtype
instance [Zero (Fin 4)]: TopologicalSpace (Thirdchart) :=
  instTopologicalSpaceSubtype
instance [Zero (Fin 4)]: TopologicalSpace (Fourthchart) :=
  instTopologicalSpaceSubtype



/-!
### Charted space structure on the SL(2,ℝ )

In this section we construct a charted space structure on the SL(2,ℝ ) in a finite-dimensional
real space `E`; that is, we show that it is locally homeomorphic to the Euclidean
space of dimension one less than `E`.
-/
section ChartedSpace

instance chartedSpace  :
    ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Special_lineargroup_order_2) where
  atlas := sorry
  chartAt v := sorry
  mem_chart_source v :=sorry
  chart_mem_atlas v :=sorry

section SmoothManifold
