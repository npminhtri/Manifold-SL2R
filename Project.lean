import Project.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.LocalHomeomorph
import Mathlib.Init.Align
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.LocalEquiv
import Mathlib.Topology.Sets.Opens
import Mathlib.Tactic
def hello_world := hello ++ " world"

universe u
open TopologicalSpace
noncomputable section

/- Definition of SL(2,ℝ ) and charts by hand -/
def Special_lineargroup_order_2 : Type :=
   { x : EuclideanSpace ℝ (Fin 4) // (x 1)*(x 4) - (x 2)*(x 3) =1 }


/- Definition of four charts that covers SL(2,ℝ )-/
def Firstcover : Type :=
  { x : EuclideanSpace ℝ (Fin 4) // (x 0)*(x 3) - (x 1)*(x 2) =1 ∧ (x 0) ≠ 0}
def Secondcover  : Type :=
  { x : EuclideanSpace ℝ (Fin 4) // (x 0)*(x 3) - (x 1)*(x 2) =1 ∧ (x 1) ≠ 0}
def Thirdcover   : Type :=
  { x : EuclideanSpace ℝ (Fin 4) // (x 0)*(x 3) - (x 1)*(x 2)  =1 ∧ (x 2) ≠ 0}
def Fourthcover : Type :=
  { x : EuclideanSpace ℝ (Fin 4) // (x 0)*(x 3) - (x 1)*(x 2) =1 ∧ (x 3) ≠ 0}
/- This is use to define a topological structure on SL(2,ℝ)
-/
section

instance : TopologicalSpace (Special_lineargroup_order_2) := instTopologicalSpaceSubtype
instance : TopologicalSpace (Firstcover) :=
  instTopologicalSpaceSubtype
instance : TopologicalSpace (Secondcover) := by apply
  instTopologicalSpaceSubtype
instance : TopologicalSpace (Thirdcover) :=
  instTopologicalSpaceSubtype
instance : TopologicalSpace (Fourthcover) :=
  instTopologicalSpaceSubtype

open scoped Manifold


/- Construction of the chart -/
def Euclideanwithoutplane0 : Type :=
  { x : EuclideanSpace ℝ (Fin 3) // 0 ≠  x 0  }

def Euclideanwithoutplane1 : Type :=
  { x : EuclideanSpace ℝ (Fin 3) // 0 ≠  x 1  }
def Euclideanwithoutplane2  [Zero (Fin 3)] : Type :=
  { x : EuclideanSpace ℝ (Fin 3) // 0 ≠  x 2  }


instance : TopologicalSpace (Euclideanwithoutplane0) :=
  instTopologicalSpaceSubtype

instance [Zero (Fin 3)]: TopologicalSpace (Euclideanwithoutplane1) :=
  instTopologicalSpaceSubtype
instance [Zero (Fin 3)]: TopologicalSpace (Euclideanwithoutplane2) :=
  instTopologicalSpaceSubtype



def Firstchart : LocalHomeomorph (Firstcover) (Euclideanwithoutplane0) where
  toFun x :={ val :=  , property:= sorry}
  invFun := sorry
  source := sorry
  target := sorry
  map_source' := sorry
  map_target' := sorry
  left_inv' := sorry
  right_inv' := sorry
  open_source := sorry
  open_target := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry


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
