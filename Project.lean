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

/-The format of  this file based on the Real.lean file (instance the the manifold of ℝ\^n )-/

/- Definition of SL(2,ℝ ) and charts by hand -/
def SL2R : Type :=
   { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z =1 }


/- Definition of four charts that covers SL(2,ℝ )-/
def Firstcover : Type :=
 { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z =1 ∧ x ≠ 0 }
def Secondcover  : Type :=
   { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z =1 ∧ y ≠ 0 }
def Thirdcover   : Type :=
  { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z =1 ∧ z ≠ 0 }
def Fourthcover : Type :=
  { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z =1 ∧ t ≠ 0 }
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
  { (x, y, z) : ℝ × ℝ × ℝ  | y ≠ 0 }
def Euclideanwithoutplane2  [Zero (Fin 3)] : Type :=
 { (x, y, z) : ℝ × ℝ × ℝ  | z ≠ 0 }

def Projection43 (x: EuclideanSpace ℝ (Fin 4) ) :

instance : TopologicalSpace (Euclideanwithoutplane0) :=
  instTopologicalSpaceSubtype

instance : TopologicalSpace (Euclideanwithoutplane1) :=
  instTopologicalSpaceSubtype
instance : TopologicalSpace (Euclideanwithoutplane2) :=
  instTopologicalSpaceSubtype





/- Define the homeomorphism between each cover and a subet set in ℝ³. Here phij denotes the map of i-th cover
### The map of 1st cover
-/
@[simp]
def prodfst (a: ℝ × ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ :=  (a.1, a.2.1,a.2.2.1)
@[simp]
def inversefst (a: ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ × ℝ := (a.1, a.2.1, a.2.2, (1+a.2.1*a.2.2)/(a.1))

/- If a vector ∈ ℝ⁴ has nonzero first coordinate, then so is it projection on the space spanned by the first three coordinate -/
@[simp]
theorem nonzerofst (a: ℝ × ℝ × ℝ × ℝ )(ha: a.1 ≠ 0) : prodfst a ∈ {(x,y,z): ℝ × ℝ × ℝ | x ≠0 } := by
  intro B; exact ha B

/- If the first coordiate is nonzero, we can go back to the First cover -/
@[simp]
theorem nonzerofst1 (a: ℝ × ℝ × ℝ   )(ha: a.1 ≠ 0) :
inversefst a ∈  { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z=1 }:= by
  simp;
  field_simp; ring_nf





def phi1 (x: ℝ × ℝ × ℝ )(hx: x.1 ≠ 0): PartialHomeomorph (SL2R) (ℝ × ℝ × ℝ ) where
  toFun a := by
    constructor
    . exact a.1.1
    . refine (a.1.2.1, a.1.2.1)
  invFun  := by
    intro a
    constructor
    . apply nonzerofst1 x; exact hx
  source := by exact Set.univ
  target := by exact Set.univ
  map_source' := by simp
  map_target' := by simp
  left_inv' x:= by simp; ring_nf; sorry
  right_inv' := by sorry
  open_source := by simp
  open_target := by simp
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := by simp; sorry

/-### The map of 2nd cover -/
@[simp]
def prodsnd (a: ℝ × ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ :=  (a.1, a.2.1,a.2.2.2)
@[simp]
def inversesnd (a: ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ × ℝ := (a.1, a.2.1, (-1+a.2.2*a.1)/a.2.1, a.2.2)

/- If a vector ∈ ℝ⁴ has nonzero first coordinate, then so is it projection on the space spanned by the first three coordinate -/
@[simp]
theorem nonzerosnd (a: ℝ × ℝ × ℝ × ℝ )(ha: a.2.1 ≠ 0) : prodsnd a ∈ {(x,y,z): ℝ × ℝ × ℝ | y ≠0 } := by
  exact ha
/- If the first coordiate is nonzero, we can go back to the First cover -/
@[simp]
theorem nonzerosnd1 (a: ℝ × ℝ × ℝ   )(ha: a.2.1 ≠ 0) :
inversesnd a ∈  { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z=1 ∧ y ≠ 0 }:= by
  simp;
  apply And.intro
  .field_simp; ring
  .exact ha



def phi2 : PartialHomeomorph (Secondcover) (Euclideanwithoutplane1) where
  toFun a := by
    constructor
    . apply nonzerosnd; exact a.2.2
  invFun a := by
    constructor
    apply nonzerosnd1; exact a.2
  source := by exact Set.univ
  target := by exact Set.univ
  map_source' := by simp
  map_target' := by simp
  left_inv' x:= by simp; ring_nf; sorry
  right_inv' := by simp
  open_source := by simp
  open_target := by simp
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := by simp; sorry


/-### The map of 3nd cover -/
@[simp]
def prodtrd (a: ℝ × ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ :=  (a.1, a.2.2.1,a.2.2.2)
@[simp]
def inversetrd (a: ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ × ℝ := (a.1, (-1+a.2.2*a.1)/a.2.1,a.2.1 , a.2.2)

/- If a vector ∈ ℝ⁴ has nonzero first coordinate, then so is it projection on the space spanned by the first three coordinate -/
@[simp]
theorem nonzerotrd (a: ℝ × ℝ × ℝ × ℝ )(ha: a.2.2.1 ≠ 0) : prodtrd a ∈ {(x,y,z): ℝ × ℝ × ℝ | y ≠0 } := by
  exact ha
/- If the first coordiate is nonzero, we can go back to the First cover -/
@[simp]
theorem nonzerotrd1 (a: ℝ × ℝ × ℝ   )(ha: a.2.1 ≠ 0) :
inversetrd a ∈  { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z=1 ∧ z ≠ 0 }:= by
  simp;
  apply And.intro
  .field_simp; ring
  .exact ha



def phi3 : PartialHomeomorph (Thirdcover) (Euclideanwithoutplane1) where
  toFun a := by
    constructor
    . apply nonzerotrd; exact a.2.2
  invFun a := by
    constructor
    apply nonzerotrd1; exact a.2
  source := by exact Set.univ
  target := by exact Set.univ
  map_source' := by simp
  map_target' := by simp
  left_inv' x:= by simp; ring_nf; sorry
  right_inv' := by simp
  open_source := by simp
  open_target := by simp
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := by simp; sorry


/-### The map of 4th cover -/
@[simp]
def prodfrth (a: ℝ × ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ :=  (a.2.1, a.2.2.1,a.2.2.2)
@[simp]
def inversefrth (a: ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ × ℝ := ((1+a.2.1*a.1)/a.2.2, a.1,a.2.1 , a.2.2)

/- If a vector ∈ ℝ⁴ has nonzero first coordinate, then so is it projection on the space spanned by the first three coordinate -/
@[simp]
theorem nonzerofrth (a: ℝ × ℝ × ℝ × ℝ )(ha: a.2.2.2 ≠ 0) : prodfrth a ∈ {(x,y,z): ℝ × ℝ × ℝ | z ≠0 } := by
  exact ha
/- If the first coordiate is nonzero, we can go back to the First cover -/
@[simp]
theorem nonzerofrth1 (a: ℝ × ℝ × ℝ   )(ha: a.2.2 ≠ 0) :
inversefrth a ∈  { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z=1 ∧ t ≠ 0 }:= by
  simp;
  apply And.intro
  .field_simp; ring
  .exact ha



def phi4 : PartialHomeomorph (Fourthcover) (Euclideanwithoutplane2) where
  toFun a := by
    constructor
    . apply nonzerofrth; exact a.2.2
  invFun a := by
    constructor
    apply nonzerofrth1; exact a.2
  source := by exact Set.univ
  target := by exact Set.univ
  map_source' := by simp
  map_target' := by simp
  left_inv' x:= by simp; ring_nf; sorry
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
