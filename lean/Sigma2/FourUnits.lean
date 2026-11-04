import Sigma2.QubitUnits
noncomputable section
open scoped BigOperators
namespace Sigma2.FourUnits
open PauliMatrixUnits QubitUnits

structure TwoPairs (e X1 Z1 X2 Z2 : Op) : Prop where
  first : Pair e X1 Z1
  second : Pair e X2 Z2
  XX : Commute X1 X2
  XZ : Commute X1 Z2
  ZX : Commute Z1 X2
  ZZ : Commute Z1 Z2

theorem commute_projector (A e Z : Op) (he : Commute A e) (hz : Commute A Z) (a : Fin 2) :
    Commute A (projector e Z a) :=
  (he.add_right (hz.smul_right (if a=0 then (1:ℂ) else -1))).smul_right (1/2:ℂ)

theorem commute_unit (A e X Z : Op) (he : Commute A e) (hx : Commute A X)
    (hz : Commute A Z) (a b : Fin 2) : Commute A (qubitUnit e X Z a b) := by
  unfold qubitUnit
  split_ifs
  · exact commute_projector A e Z he hz b
  · exact hx.mul_right (commute_projector A e Z he hz b)

theorem cross_units (e X1 Z1 X2 Z2 : Op) (h : TwoPairs e X1 Z1 X2 Z2)
    (a b c d : Fin 2) : Commute (qubitUnit e X1 Z1 a b) (qubitUnit e X2 Z2 c d) := by
  have he : Commute e (qubitUnit e X2 Z2 c d) :=
    commute_unit e e X2 Z2 (Commute.refl e)
      (h.second.eX.trans h.second.Xe.symm) (h.second.eZ.trans h.second.Ze.symm) c d
  have hx : Commute X1 (qubitUnit e X2 Z2 c d) :=
    commute_unit X1 e X2 Z2 (h.first.Xe.trans h.first.eX.symm) h.XX h.XZ c d
  have hz : Commute Z1 (qubitUnit e X2 Z2 c d) :=
    commute_unit Z1 e X2 Z2 (h.first.Ze.trans h.first.eZ.symm) h.ZX h.ZZ c d
  exact (commute_unit _ e X1 Z1 he.symm hx.symm hz.symm a b).symm

abbrev Index := Fin 2 × Fin 2

def matrixUnit (e X1 Z1 X2 Z2 : Op) (i j : Index) : Op :=
  qubitUnit e X1 Z1 i.1 j.1*qubitUnit e X2 Z2 i.2 j.2

def diagonal (e Z1 Z2 : Op) (i : Index) : Op :=
  projector e Z1 i.1*projector e Z2 i.2

theorem matrix_product (e X1 Z1 X2 Z2 : Op) (h : TwoPairs e X1 Z1 X2 Z2) (i j k l : Index) :
    matrixUnit e X1 Z1 X2 Z2 i j*matrixUnit e X1 Z1 X2 Z2 k l=
      if j=k then matrixUnit e X1 Z1 X2 Z2 i l else 0 := by
  unfold matrixUnit
  calc
    _ = (qubitUnit e X1 Z1 i.1 j.1*qubitUnit e X1 Z1 k.1 l.1)*
        (qubitUnit e X2 Z2 i.2 j.2*qubitUnit e X2 Z2 k.2 l.2) := by
      have hc := (cross_units e X1 Z1 X2 Z2 h k.1 l.1 i.2 j.2).eq
      calc
        _ = qubitUnit e X1 Z1 i.1 j.1*(qubitUnit e X2 Z2 i.2 j.2*qubitUnit e X1 Z1 k.1 l.1)*
            qubitUnit e X2 Z2 k.2 l.2 := by noncomm_ring
        _ = _ := by rw [← hc]; noncomm_ring
    _ = _ := by
      rw [qubit_product e X1 Z1 h.first,qubit_product e X2 Z2 h.second]
      by_cases h1 : j.1=k.1 <;> by_cases h2 : j.2=k.2 <;>
        simp [h1,h2,Prod.ext_iff]

theorem matrix_star (e X1 Z1 X2 Z2 : Op) (h : TwoPairs e X1 Z1 X2 Z2) (i j : Index) :
    star (matrixUnit e X1 Z1 X2 Z2 i j)=matrixUnit e X1 Z1 X2 Z2 j i := by
  unfold matrixUnit
  rw [star_mul,qubit_star e X1 Z1 h.first,qubit_star e X2 Z2 h.second]
  exact (cross_units e X1 Z1 X2 Z2 h j.1 i.1 j.2 i.2).eq.symm

theorem matrix_diagonal (e X1 Z1 X2 Z2 : Op) (i : Index) :
    matrixUnit e X1 Z1 X2 Z2 i i=diagonal e Z1 Z2 i := by simp only [matrixUnit,diagonal,qubit_diagonal]

theorem matrix_sum (e X1 Z1 X2 Z2 : Op) (h : TwoPairs e X1 Z1 X2 Z2) :
    ∑ i : Index,matrixUnit e X1 Z1 X2 Z2 i i=e := by
  simp only [matrixUnit,Fintype.sum_prod_type,← Finset.mul_sum,qubit_sum,← Finset.sum_mul,h.first.projection.2]

/-- Construct the four-by-four units on the actual magic corner. -/
theorem actual_matrix_units {s} (S : PureStrategy s) (I : Compiler.FMSInstance s)
    (hS : Compiler.ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : Preliminaries.SupportOf h P) :
    let e := MagicCells.rowActive S I P 0
    let C := MagicCells.rowCell S I P
    let t := matrixUnit e (C 1 1) (C 0 0) (C 0 1) (C 1 0)
    (∀ i j k l,t i j*t k l=if j=k then t i l else 0) ∧
      (∀ i j,star (t i j)=t j i) ∧ (∑ i,t i i)=e := by
  obtain ⟨h1,h2,hxx,hxz,hzx,hzz⟩ := actual_pauli_pairs S I hS h hm P hP
  have hp : TwoPairs (MagicCells.rowActive S I P 0) (MagicCells.rowCell S I P 1 1)
      (MagicCells.rowCell S I P 0 0) (MagicCells.rowCell S I P 0 1) (MagicCells.rowCell S I P 1 0) :=
    ⟨h1,h2,hxx,hxz,hzx,hzz⟩
  exact ⟨matrix_product _ _ _ _ _ hp,matrix_star _ _ _ _ _ hp,matrix_sum _ _ _ _ _ hp⟩

#print axioms actual_matrix_units
end Sigma2.FourUnits
