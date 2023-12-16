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


/- This is use to define a topological structure on SL(2,ℝ)
-/

section

instance : TopologicalSpace (SL2R) := instTopologicalSpaceSubtype

open scoped Manifold




def Euclideanwithoutplane : Type:= { (x, y, z) : ℝ × ℝ × ℝ  | x ≠ 0 ∨   y ≠ 0 ∨ z ≠ 0 }

instance : TopologicalSpace (Euclideanwithoutplane) :=
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
theorem nonzerofst (a: ℝ × ℝ × ℝ × ℝ )(ha: a.1 ≠ 0) : prodfst a ∈ {(x,y,z): ℝ × ℝ × ℝ | x ≠0 ∨ y ≠ 0 ∨ z ≠ 0 } :=
 by constructor; exact ha


/- If the first coordiate is nonzero, we can go back to the First cover -/
@[simp]
theorem nonzerofst1 (a: ℝ × ℝ × ℝ   )(ha: a.1 ≠ 0) :
inversefst a ∈  { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z=1 }:= by
  simp;
  field_simp; ring_nf

/-### The map of 2nd cover -/
@[simp]
def prodsnd (a: ℝ × ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ :=  (a.1, a.2.1,a.2.2.2)
@[simp]
def inversesnd (a: ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ × ℝ := (a.1, a.2.1, (-1+a.2.2*a.1)/a.2.1, a.2.2)

/- If a vector ∈ ℝ⁴ has nonzero first coordinate, then so is it projection on the space spanned by the first three coordinate -/
@[simp]
theorem nonzerosnd (a: ℝ × ℝ × ℝ × ℝ )(ha: a.2.1 ≠  0) :
prodsnd a ∈ {(x,y,z): ℝ × ℝ × ℝ | x ≠ 0 ∨ y ≠0 ∨ z ≠ 0 } :=
  by dsimp; refine Or.inr ?h; exact Or.inl ha
/- If the first coordiate is nonzero, we can go back to the First cover -/
@[simp]
theorem nonzerosnd1 (a: ℝ × ℝ × ℝ   )(ha: a.2.1 ≠ 0) :
inversesnd a ∈  { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z=1 ∧ y ≠ 0 }:= by
  simp;
  apply And.intro
  .field_simp; ring
  .exact ha

/-### The map of 3nd cover -/
@[simp]
def prodtrd (a: ℝ × ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ :=  (a.1, a.2.2.1,a.2.2.2)
@[simp]
def inversetrd (a: ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ × ℝ := (a.1, (-1+a.2.2*a.1)/a.2.1,a.2.1 , a.2.2)

/- If a vector ∈ ℝ⁴ has nonzero first coordinate, then so is it projection on the space spanned by the first three coordinate -/
@[simp]
theorem nonzerotrd (a: ℝ × ℝ × ℝ × ℝ )(ha: a.2.2.1 ≠ 0) : prodtrd a ∈ {(x,y,z): ℝ × ℝ × ℝ | x ≠ 0 ∨ y ≠0 ∨ z ≠ 0 } :=
 by simp; refine Or.inr ?h; exact Or.inl ha
/- If the first coordiate is nonzero, we can go back to the First cover -/
@[simp]
theorem nonzerotrd1 (a: ℝ × ℝ × ℝ   )(ha: a.2.1 ≠ 0) :
inversetrd a ∈  { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z=1 ∧ z ≠ 0 }:= by
  simp;
  apply And.intro
  .field_simp; ring
  .exact ha

/-### The map of 4th cover -/
@[simp]
def prodfrth (a: ℝ × ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ :=  (a.2.1, a.2.2.1,a.2.2.2)
@[simp]
def inversefrth (a: ℝ × ℝ × ℝ  ) :ℝ × ℝ × ℝ × ℝ := ((1+a.2.1*a.1)/a.2.2, a.1,a.2.1 , a.2.2)

/- If a vector ∈ ℝ⁴ has nonzero first coordinate, then so is it projection on the space spanned by the first three coordinate -/
@[simp]
theorem nonzerofrth (a: ℝ × ℝ × ℝ × ℝ )(ha: a.2.2.2 ≠ 0) : prodfrth a ∈ {(x,y,z): ℝ × ℝ × ℝ | x ≠ 0 ∨ y ≠0 ∨ z ≠ 0 }  := by
simp; refine Or.inr ?h; exact Or.inr ha
/- If the first coordiate is nonzero, we can go back to the First cover -/
@[simp]
theorem nonzerofrth1 (a: ℝ × ℝ × ℝ   )(ha: a.2.2 ≠ 0) :
inversefrth a ∈  { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*t-y*z=1 ∧ t ≠ 0 }:= by
  simp;
  apply And.intro
  .field_simp; ring
  .exact ha

/-# Partition lemma-/
/- Here I want to show that if x ∈ SL2R then x is nonzero, hence there must be a nonzero coordinate -/
lemma zero (x: ℝ × ℝ × ℝ ×ℝ  )(hx: x.1 = 0 ∧ x.2.1=0 ∧ x.2.2.1 =0 ∧ x.2.2.2 =0): x = 0:=by
ext
apply And.left hx
apply And.left (And.right hx)
apply And.left (And.right (And.right hx))
apply (hx.right).right.right

lemma partition (x: SL2R): x.1 ≠ 0 ∨ x.1.2.1 ≠0 ∨ x.1.2.2.1 ≠ 0 ∨ x.1.2.2.2 ≠ 0 :=by sorry




#check Set (SL2R)

/-# Define the atlas-/


def Firstcover : PartialHomeomorph (SL2R) (Euclideanwithoutplane ) where
  toFun a :=by sorry
  invFun x := by
    constructor
    .sorry
    .apply inversefst x.1
  source :=  by exact Set.univ
  target := by exact Set.univ
  map_source' := by simp
  map_target' := by simp
  left_inv' x:= by simp; ring_nf; sorry
  right_inv' := by simp; sorry
  open_source := by simp
  open_target := by simp
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := by simp; sorry





def Secondcover : PartialHomeomorph (SL2R) (Euclideanwithoutplane ) where
  toFun a := by
    constructor
    .apply nonzerofst a.1;
  invFun x := by
    constructor
    .sorry
    .apply inversefst x.1
  source := by exact Set.univ
  target := by exact Set.univ
  map_source' := by simp
  map_target' := by simp
  left_inv' x:= by simp; ring_nf; sorry
  right_inv' := by simp;
  open_source := by simp
  open_target := by simp
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := by simp; sorry




def Thirdcover : PartialHomeomorph (SL2R) (Euclideanwithoutplane ) where
  toFun a := by
    constructor
    .apply nonzerofst a.1; sorry
  invFun x := by
    constructor
    .sorry
    .apply inversefst x.1
  source := by exact Set.univ
  target := by exact Set.univ
  map_source' := by simp
  map_target' := by simp
  left_inv' x:= by simp; ring_nf; sorry
  right_inv' := by simp;
  open_source := by simp
  open_target := by simp
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := by simp; sorry





def Fourthcover : PartialHomeomorph (SL2R) (Euclideanwithoutplane ) where
  toFun a := by
    constructor
    .apply nonzerofst a.1; sorry
  invFun x := by
    constructor
    .sorry
    .apply inversefst x.1
  source := by exact Set.univ
  target := by exact Set.univ
  map_source' := by simp
  map_target' := by simp
  left_inv' x:= by simp; ring_nf; sorry
  right_inv' := by simp;
  open_source := by simp
  open_target := by simp
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := by simp; sorry






/-!
### Charted space structure on the SL(2,ℝ )

In this section we construct a charted space structure on the SL(2,ℝ ) in a finite-dimensional
real space `ℝ × ℝ × ℝ   `.
-/
section ChartedSpace

instance chartedSpace  :
    ChartedSpace  (Euclideanwithoutplane ) (SL2R) where
  atlas := {Firstcover, Secondcover, Thirdcover, Fourthcover}
  chartAt v := if v.1 ≠ 0 then Firstcover
            else if v.1.2.1 ≠ 0 then Secondcover else if v.1.2.2.1 ≠ 0 then Thirdcover else Fourthcover
  mem_chart_source v := by simp; sorry
  chart_mem_atlas v := by simp; constructor; sorry

section SmoothManifold
