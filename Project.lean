import Project.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Topology.Sets.Opens
import Mathlib.Init.Align
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Sets.Opens
import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

def hello_world := hello ++ " world"

universe u
open TopologicalSpace
noncomputable section

/- Definition of SL(2,ℝ ) and charts by hand -/
def SL2R : Type :=
   { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*z-y*t =1 }


/- Definition of four charts that covers SL(2,ℝ )-/
def Firstcover : Type :=
 { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z =1 ∧ x ≠ 0 }
def Secondcover  : Type :=
  { x : EuclideanSpace ℝ (Fin 4) // (x 0)*(x 3) - (x 1)*(x 2) =1 ∧ (x 1) ≠ 0}
def Thirdcover   : Type :=
  { x : EuclideanSpace ℝ (Fin 4) // (x 0)*(x 3) - (x 1)*(x 2)  =1 ∧ (x 2) ≠ 0}
def Fourthcover : Type :=
  { x : EuclideanSpace ℝ (Fin 4) // (x 0)*(x 3) - (x 1)*(x 2) =1 ∧ (x 3) ≠ 0}
/- This is use to define a topological structure on SL(2,ℝ)
-/

section

instance : TopologicalSpace (SL2R) := instTopologicalSpaceSubtype
instance : TopologicalSpace (Firstcover) := instTopologicalSpaceSubtype
instance : TopologicalSpace (Secondcover) := by apply
  instTopologicalSpaceSubtype
instance : TopologicalSpace (Thirdcover) :=
  instTopologicalSpaceSubtype
instance : TopologicalSpace (Fourthcover) :=
  instTopologicalSpaceSubtype

open scoped Manifold


/- Construction of the chart -/
def Euclideanwithoutplane0 : Type :=
 { (x, y, z) : ℝ × ℝ × ℝ  | x ≠ 0 }

def Euclideanwithoutplane1 : Type :=
  { x : EuclideanSpace ℝ (Fin 3) // 0 ≠  x 1  }
def Euclideanwithoutplane2  [Zero (Fin 3)] : Type :=
  { x : EuclideanSpace ℝ (Fin 3) // 0 ≠  x 2  }

def Projection43 (x: EuclideanSpace ℝ (Fin 4) ) :

instance : TopologicalSpace (Euclideanwithoutplane0) :=
  instTopologicalSpaceSubtype

instance : TopologicalSpace (Euclideanwithoutplane1) :=
  instTopologicalSpaceSubtype
instance : TopologicalSpace (Euclideanwithoutplane2) :=
  instTopologicalSpaceSubtype

variable (a: Firstcover)
#check a.2.2

@[simp]
def prodfst (a: ℝ × ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ :=  (a.1, a.2.1,a.2.2.1)
@[simp]
def inversefst (a: ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ × ℝ := (a.1, a.2.1, a.2.2, (1+a.2.1*a.2.2)/(a.1))

/- If a vector ∈ ℝ⁴ has nonzero first coordinate, then so is it projection on the space spanned by the first three coordinate -/
@[simp]
theorem nonzerofst (a: ℝ × ℝ × ℝ × ℝ )(ha: a.1 ≠ 0) : prodfst a ∈ {(x,y,z): ℝ × ℝ × ℝ | x ≠0 } := by
  intro B; exact ha B

@[simp]
theorem nonzerofst1 (a: ℝ × ℝ × ℝ   )(ha: a.1 ≠ 0) :
inversefst a ∈  { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z=1 ∧ x ≠ 0 }:= by
  simp;
  apply And.intro
  .field_simp; ring
  .exact ha



def phi1 : PartialHomeomorph (Firstcover) (Euclideanwithoutplane0) where
  toFun a := by
    constructor
    . apply nonzerofst; exact a.2.2
  invFun a := by
    constructor
    apply nonzerofst1; exact a.2
  source := by exact Set.univ
  target := by exact Set.univ
  map_source' := by simp
  map_target' := by simp
  left_inv' := by simp; intro x; ring_nf; sorry
  right_inv' := by simp
  open_source := by simp
  open_target := by simp
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := by simp; sorry



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
