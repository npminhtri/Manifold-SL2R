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

open TopologicalSpace
noncomputable section

/-The format of  this file based on the Real.lean file (instance the the manifold of ℝ\^n )-/

/- Definition of SL(2,ℝ ) and charts by hand -/
def SL2R : Type :=
   { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*y-z*t =1 }
deriving TopologicalSpace

instance : Inhabited SL2R := ⟨⟨(1,1,0,0), by simp⟩⟩


theorem elementSL2R (b:ℝ × ℝ × ℝ × ℝ) (hb : b ∈ { (x, y, z,t) : ℝ × ℝ × ℝ × ℝ | x*y-z*t =1 }):
1 = b.1*b.2.1-b.2.2.1 * b.2.2.2:=by exact
  ((fun {z} => Complex.ofReal_eq_one.mp) (congrArg Complex.ofReal' hb)).symm



@[ext]
theorem SL2R.ext (x y: SL2R)(h1: x.1 = y.1) : x = y := by exact Subtype.eq h1

@[simp]
theorem SL2R.eq1 (x: SL2R) : 1 + x.1.2.2.1 * x.1.2.2.2 = x.1.1*x.1.2.1 :=by
  have h:  1 = x.1.1*x.1.2.1-x.1.2.2.1 * x.1.2.2.2
  . apply elementSL2R; exact x.property
  .exact add_eq_of_eq_sub h
@[simp]
theorem SL2R.eq2 (x: SL2R) :   x.1.1*x.1.2.1 - 1 =x.1.2.2.1 * x.1.2.2.2 :=by
  have h:  1 = x.1.1*x.1.2.1-x.1.2.2.1 * x.1.2.2.2
  . apply elementSL2R; exact x.property
  . ring_nf; rw [@neg_add_eq_iff_eq_add]; rw [eq1]


theorem SL2Rzero (x: SL2R)(hx: x.1.1 =0): x.1.2.2.1 ≠ 0:= by
have:  1 = x.1.1*x.1.2.1-x.1.2.2.1 * x.1.2.2.2
.apply elementSL2R; exact x.property
.rw[hx] at this; simp at this; intro a; rw[a] at this; simp at this

def chart1 : PartialHomeomorph SL2R (ℝ × ℝ × ℝ) where
  toFun := fun ⟨(x,y,z,w),h⟩ => (x,z,w)
  invFun := fun (x,z,w) => if h : x = 0 then default else ⟨(x,(1+z*w)/x,z,w), by field_simp ; ring⟩
  source := { ⟨(x,y,z,w),h⟩ : SL2R | x ≠ 0 }
  target := { (x,y,z) : ℝ × ℝ ×ℝ | x ≠ 0  }
  map_source' := by intro x hx;simp; intro a; apply hx a
  map_target' x hx := by simp; sorry
  left_inv' x hx := by
    refine dite_eq_iff'.mpr ?_
    apply And.intro
    .exact fun h => (hx h).elim
    . field_simp
      intro H
      ext; simp; field_simp; rw[mul_comm ]; simp; simp
  right_inv' x hx := by
    field_simp
    ext
    .sorry
    .sorry
    .sorry
  open_source := by
    simp
    refine IsClosed.not ?_
    refine isClosed_induced_iff.mpr ?_
    let t:={(x,y,z,t): ℝ × ℝ × ℝ × ℝ| x = 0}
    use t
    constructor
    .sorry
    .sorry
  open_target :=  by dsimp; refine IsClosed.not ?_; refine IsSeqClosed.isClosed ?hs; sorry
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := sorry

def chart2 : PartialHomeomorph SL2R (ℝ × ℝ × ℝ) where
  toFun := fun ⟨(x,y,z,w),h⟩ => (y,z,w)
  invFun := fun (y,z,w) => if h : y = 0 then default else ⟨((1+z*w)/y,y,z,w), by field_simp ; ring⟩
  source := { ⟨(x,y,z,w),h⟩ : SL2R | y ≠ 0 }
  target := { (y,z,w) : ℝ × ℝ ×ℝ | y ≠ 0  }
  map_source' := by intro x hx;simp; intro a; apply hx a
  map_target' x hx := by simp; sorry
  left_inv' x hx := by
    refine dite_eq_iff'.mpr ?_
    apply And.intro
    .exact fun h => (hx h).elim
    . field_simp
  right_inv' x hx := by
    field_simp
    ext
    .sorry
    .sorry
    .sorry
  open_source := by
    simp
    refine IsClosed.not ?_
    refine isClosed_induced_iff.mpr ?_
    let t:={(x,y,z,t): ℝ × ℝ × ℝ × ℝ| x = 0}
    use t
    constructor
    .sorry
    .sorry
  open_target :=  by dsimp; refine IsClosed.not ?_; refine IsSeqClosed.isClosed ?hs; sorry
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := sorry

def chart3 : PartialHomeomorph SL2R (ℝ × ℝ × ℝ) where
  toFun := fun ⟨(x,y,z,w),h⟩ => (x,y,z)
  invFun := fun (x,y,z) => if h :  z = 0 then default else ⟨(x,y,z,(x*y-1)/z), by field_simp ; ring⟩
  source := { ⟨(x,y,z,w),h⟩ : SL2R | z ≠ 0 }
  target := { (x,y,z) : ℝ × ℝ ×ℝ | z ≠ 0  }
  map_source' := by intro x hx;simp; intro a; apply hx a
  map_target' x hx := by simp; sorry
  left_inv' x hx := by
    refine dite_eq_iff'.mpr ?_
    apply And.intro
    .exact fun h => (hx h).elim
    .intro h; ext; simp; simp; simp; field_simp; rw[mul_comm]
  right_inv' x hx := by
    field_simp
    ext
    .sorry
    .sorry
    .sorry
  open_source := by
    simp
    refine IsClosed.not ?_
    refine isClosed_induced_iff.mpr ?_
    let t:={(x,y,z,t): ℝ × ℝ × ℝ × ℝ| x = 0}
    use t
    constructor
    .sorry
    .sorry
  open_target :=  by dsimp; refine IsClosed.not ?_; refine IsSeqClosed.isClosed ?hs; sorry
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := sorry


def chart4 : PartialHomeomorph SL2R (ℝ × ℝ × ℝ) where
  toFun := fun ⟨(x,y,z,w),h⟩ => (x,y,w)
  invFun := fun (x,y,w) => if h :  w = 0 then default else ⟨(x,y,(x*y-1)/w,w), by field_simp⟩
  source := { ⟨(x,y,z,w),h⟩ : SL2R | w ≠ 0 }
  target := { (x,y,w) : ℝ × ℝ ×ℝ | w ≠ 0  }
  map_source' := by intro x hx;simp; intro a; apply hx a
  map_target' x hx := by simp; sorry
  left_inv' x hx := by
    refine dite_eq_iff'.mpr ?_
    apply And.intro
    .exact fun h => (hx h).elim
    .intro h; ext; simp; simp; field_simp; simp
  right_inv' x hx := by
    field_simp
    ext
    .sorry
    .sorry
    .sorry
  open_source := by
    simp
    refine IsClosed.not ?_
    refine isClosed_induced_iff.mpr ?_
    let t:={(x,y,z,t): ℝ × ℝ × ℝ × ℝ| x = 0}
    use t
    constructor
    .sorry
    .sorry
  open_target :=  by dsimp; refine IsClosed.not ?_; refine IsSeqClosed.isClosed ?hs; sorry
  continuousOn_toFun := by simp; sorry
  continuousOn_invFun := by simp; sorry

/-!
### Charted space structure on the SL(2,ℝ )

In this section we construct a charted space structure on the SL(2,ℝ ) in a finite-dimensional
real space `ℝ × ℝ × ℝ   `.
-/
section ChartedSpace
variable (a: SL2R)
#check a.1.1
instance chartedSpace  :
    ChartedSpace  (ℝ × ℝ × ℝ) (SL2R) where
  atlas := { chart1,chart3}
  chartAt v := if v.1.1 ≠ 0 then chart1 else chart3
  mem_chart_source v := by
    by_cases h': v.1.1 = 0
    · simp[h']; intro a; apply SL2Rzero; exact h'; exact a
    · simp[h']; intro a; exact h' a
  chart_mem_atlas v := by by_cases h': v.1.1 = 0 ; simp[h']; simp[h']

section SmoothManifold
