import Sigma2.RowScalarJoints
import Sigma2.MatrixCentralizer

noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame CoarseCells FiniteSpectral FourUnits

def localUnit (G : Game) (R : Rows G.scenario) (M : Measurements (scenario G R))
    (P : Op) (g : Fin (RowSlots.squares R)) (i j : FourUnits.Index) : Op :=
  FourUnits.matrixUnit P (binary G R M P (axisQ R g 2)) (binary G R M P (axisQ R g 0))
    (binary G R M P (axisQ R g 3)) (binary G R M P (axisQ R g 1)) i j

theorem localUnit_laws (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : Preliminaries.SupportOf h P)
    (g : Fin (RowSlots.squares R)) :
    (∀ i j k l,localUnit G R S.measurements P g i j*localUnit G R S.measurements P g k l=
      if j=k then localUnit G R S.measurements P g i l else 0) ∧
    (∀ i j,star (localUnit G R S.measurements P g i j)=localUnit G R S.measurements P g j i) ∧
    (∑ i,localUnit G R S.measurements P g i i)=P := by
  have hp := measured_pauli_pairs G R S hS h hm P hP g
  exact ⟨FourUnits.matrix_product _ _ _ _ _ hp,
    FourUnits.matrix_star _ _ _ _ _ hp,FourUnits.matrix_sum _ _ _ _ _ hp⟩

theorem localUnit_supported (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : Preliminaries.SupportOf h P)
    (g : Fin (RowSlots.squares R)) (i j : FourUnits.Index) :
    P*localUnit G R S.measurements P g i j=localUnit G R S.measurements P g i j ∧
      localUnit G R S.measurements P g i j*P=localUnit G R S.measurements P g i j := by
  have hh := localUnit_laws G R S hS h hm P hP g
  constructor
  · calc
      _ = (∑ k,localUnit G R S.measurements P g k k)*localUnit G R S.measurements P g i j :=
        congrArg (fun A : Op => A*localUnit G R S.measurements P g i j) hh.2.2.symm
      _ = _ := by rw [Finset.sum_mul]; simp [hh.1]
  · calc
      _ = localUnit G R S.measurements P g i j*(∑ k,localUnit G R S.measurements P g k k) :=
        congrArg (fun A : Op => localUnit G R S.measurements P g i j*A) hh.2.2.symm
      _ = _ := by rw [Finset.mul_sum]; simp [hh.1]

theorem binary_supported (G : Game) (R : Rows G.scenario) (M : Measurements (scenario G R))
    (P : Op) (hP : Projection P) (q : NewQ R) :
    P*binary G R M P q=binary G R M P q ∧ binary G R M P q*P=binary G R M P q := by
  unfold binary signed
  rw [coarse_compressed,coarse_compressed]
  constructor
  · simp only [mul_sub,← mul_assoc,hP.2]
  · simp only [sub_mul,mul_assoc,hP.2]

theorem commute_localUnit (G : Game) (R : Rows G.scenario) (M : Measurements (scenario G R))
    (P A : Op) (g : Fin (RowSlots.squares R)) (he : Commute A P)
    (hc : ∀ k,Commute A (binary G R M P (axisQ R g k))) (i j : FourUnits.Index) :
    Commute A (localUnit G R M P g i j) := by
  exact (commute_unit A _ _ _ he (hc 2) (hc 0) i.1 j.1).mul_right
    (commute_unit A _ _ _ he (hc 3) (hc 1) i.2 j.2)

/-- The concrete scalar squares supply mutually commuting M4 factors. -/
theorem localUnit_cross (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : Preliminaries.SupportOf h P)
    (g u : Fin (RowSlots.squares R)) (hgu : g≠u) (i j k l : FourUnits.Index) :
    Commute (localUnit G R S.measurements P g i j) (localUnit G R S.measurements P u k l) := by
  have hs := localUnit_supported G R S hS h hm P hP g i j
  apply commute_localUnit G R S.measurements P _ u (hs.2.trans hs.1.symm)
  intro a
  have ha := binary_supported G R S.measurements P hP.1 (axisQ R u a)
  exact (commute_localUnit G R S.measurements P _ g (ha.2.trans ha.1.symm)
    (fun b => (cross_commute G R S hS h hm P hP g u hgu b a).symm) i j).symm

/-- Recursive tensor indices have exactly 4^r elements. -/
def Register : ℕ → Type
  | 0 => Unit
  | n+1 => FourUnits.Index × Register n

instance registerFintype (n : ℕ) : Fintype (Register n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact @instFintypeProd _ _ inferInstance ih

instance registerDecidableEq (n : ℕ) : DecidableEq (Register n) := Classical.decEq _

theorem register_card (n : ℕ) : Fintype.card (Register n)=4^n := by
  induction n with
  | zero =>
    calc
      Fintype.card (Register 0)=Fintype.card Unit := Fintype.card_congr (Equiv.refl Unit)
      _ = 1 := Fintype.card_unique
  | succ n ih => simpa [Register,Fintype.card_prod,Fintype.card_fin,pow_succ,mul_comm] using congrArg (fun v : ℕ => 4*v) ih

def tensorUnit (P : Op) : {n : ℕ} → (Fin n → FourUnits.Index → FourUnits.Index → Op) →
    Register n → Register n → Op
  | 0,_,_,_ => P
  | n+1,U,i,j => U 0 i.1 j.1*tensorUnit P (fun g => U g.succ) i.2 j.2

private theorem tensor_commute (P A : Op) {n : ℕ}
    (U : Fin n → FourUnits.Index → FourUnits.Index → Op) (he : Commute A P)
    (hc : ∀ g i j,Commute A (U g i j)) (i j : Register n) :
    Commute A (tensorUnit P U i j) := by
  induction n with
  | zero => exact he
  | succ n ih => exact (hc 0 i.1 j.1).mul_right (ih _ (fun g => hc g.succ) i.2 j.2)

private theorem tensor_supported (P : Op) (hP : P*P=P) {n : ℕ}
    (U : Fin n → FourUnits.Index → FourUnits.Index → Op)
    (hs : ∀ g i j,P*U g i j=U g i j ∧ U g i j*P=U g i j) (i j : Register n) :
    P*tensorUnit P U i j=tensorUnit P U i j ∧ tensorUnit P U i j*P=tensorUnit P U i j := by
  induction n with
  | zero => exact ⟨hP,hP⟩
  | succ n ih =>
    have ht := ih (fun g => U g.succ) (fun g => hs g.succ) i.2 j.2
    constructor
    · change P*(U 0 i.1 j.1*tensorUnit P (fun g => U g.succ) i.2 j.2)=_
      rw [← mul_assoc,(hs 0 i.1 j.1).1]; rfl
    · change (U 0 i.1 j.1*tensorUnit P (fun g => U g.succ) i.2 j.2)*P=_
      rw [mul_assoc,ht.2]; rfl

private theorem tensor_laws (P : Op) (hP : Projection P) {n : ℕ}
    (U : Fin n → FourUnits.Index → FourUnits.Index → Op)
    (hs : ∀ g i j,P*U g i j=U g i j ∧ U g i j*P=U g i j)
    (hp : ∀ g i j k l,U g i j*U g k l=if j=k then U g i l else 0)
    (hst : ∀ g i j,star (U g i j)=U g j i)
    (hsm : ∀ g,(∑ i,U g i i)=P)
    (hc : ∀ g u,g≠u → ∀ i j k l,Commute (U g i j) (U u k l)) :
    (∀ i j k l,tensorUnit P U i j*tensorUnit P U k l=if j=k then tensorUnit P U i l else 0) ∧
      (∀ i j,star (tensorUnit P U i j)=tensorUnit P U j i) ∧
      (∑ i,tensorUnit P U i i)=P := by
  induction n with
  | zero =>
    refine ⟨?_,?_,?_⟩
    · intro i j k l; have hj : j=k := @Subsingleton.elim Unit _ _ _; simp [tensorUnit,hj,hP.2]
    · intro i j; exact hP.1
    · simp only [tensorUnit,Finset.sum_const,Finset.card_univ,register_card,pow_zero,one_nsmul]
  | succ n ih =>
    have ht := ih (fun g => U g.succ) (fun g => hs g.succ) (fun g => hp g.succ)
      (fun g => hst g.succ) (fun g => hsm g.succ)
      (fun g u hgu => hc g.succ u.succ (by intro he; exact hgu (Fin.succ_injective _ he)))
    have hcross (i j : FourUnits.Index) (k l : Register n) :
        Commute (U 0 i j) (tensorUnit P (fun g => U g.succ) k l) :=
      tensor_commute P (U 0 i j) _ ((hs 0 i j).2.trans (hs 0 i j).1.symm)
        (fun g k l => hc 0 g.succ (by intro he; have hv := congrArg Fin.val he; simp at hv) i j k l) k l
    refine ⟨?_,?_,?_⟩
    · intro i j k l
      change (U 0 i.1 j.1*tensorUnit P (fun g => U g.succ) i.2 j.2)*
        (U 0 k.1 l.1*tensorUnit P (fun g => U g.succ) k.2 l.2)=_
      calc
        _ = (U 0 i.1 j.1*U 0 k.1 l.1)*
          (tensorUnit P (fun g => U g.succ) i.2 j.2*tensorUnit P (fun g => U g.succ) k.2 l.2) := by
          rw [mul_assoc,← mul_assoc (tensorUnit P (fun g => U g.succ) i.2 j.2),← (hcross k.1 l.1 i.2 j.2).eq]
          noncomm_ring
        _ = _ := by
          rw [hp,ht.1]
          have heq : j=k ↔ j.1=k.1 ∧ j.2=k.2 := Prod.ext_iff
          by_cases h1 : j.1=k.1 <;> by_cases h2 : j.2=k.2 <;>
            simp [heq,h1,h2,tensorUnit]
    · intro i j
      change star (U 0 i.1 j.1*tensorUnit P (fun g => U g.succ) i.2 j.2)=_
      rw [star_mul,hst,ht.2.1]
      exact (hcross j.1 i.1 j.2 i.2).eq.symm
    · change (∑ i : FourUnits.Index × Register n,U 0 i.1 i.1*tensorUnit P (fun g => U g.succ) i.2 i.2)=P
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum,ht.2.2,← Finset.sum_mul,hsm,hP.2]

/-- A single complete M_(4^r) system on the original normal support, derived
from all concrete square and cross-square questions. No decomposition is supplied
as a premise, and there is no density inverse or dimension bound. -/
theorem common_matrix_units (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : Preliminaries.SupportOf h P) :
    let t := tensorUnit P (localUnit G R S.measurements P)
    (∀ i j k l,t i j*t k l=if j=k then t i l else 0) ∧
      (∀ i j,star (t i j)=t j i) ∧ (∑ i,t i i)=P := by
  exact tensor_laws P hP.1 _
    (localUnit_supported G R S hS h hm P hP)
    (fun g => (localUnit_laws G R S hS h hm P hP g).1)
    (fun g => (localUnit_laws G R S hS h hm P hP g).2.1)
    (fun g => (localUnit_laws G R S hS h hm P hP g).2.2)
    (localUnit_cross G R S hS h hm P hP)




private theorem pure_cells_centralize (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : Preliminaries.SupportOf h P)
    (g : Fin (RowSlots.squares R)) (x y : Fin 3) :
    Commute h.op (cells G R S.measurements P g x y) := by
  have hp := MatrixCentralizer.support_centralizes h P hP
  have h1 := (context_analysis G R S hS h hm P hP g false x y 1).2.2.2
  have h2 := (context_analysis G R S hS h hm P hP g false x y 2).2.2.2
  change Commute h.op (coarse (compressed P _) _ 1-coarse (compressed P _) _ 2)
  rw [coarse_compressed,coarse_compressed]
  exact ((hp.mul_right h1).mul_right hp).sub_right ((hp.mul_right h2).mul_right hp)

theorem cells_centralize (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : Preliminaries.SupportOf h P)
    (g : Fin (RowSlots.squares R)) (x y : Fin 3) :
    Commute h.op (cells G R S.measurements P g x y) := by
  obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
  have hh := pure_cells_centralize G R T (pure_perfect_transfer G R S hS T hprob)
    h (hM h hm) P hP g x y
  simpa only [cells,context,hA] using hh

theorem axes_centralize (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : Preliminaries.SupportOf h P)
    (g : Fin (RowSlots.squares R)) (k : Fin 4) :
    Commute h.op (binary G R S.measurements P (axisQ R g k)) := by
  unfold axisQ
  split_ifs <;> rw [← cells_identify G R S hS h hm P hP] <;>
    exact cells_centralize G R S hS h hm P hP _ _ _

/-- The original normal density centralizes every common scalar matrix unit. -/
theorem common_units_centralize (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : Preliminaries.SupportOf h P)
    (i j : Register (RowSlots.squares R)) :
    Commute h.op (tensorUnit P (localUnit G R S.measurements P) i j) := by
  have hp := MatrixCentralizer.support_centralizes h P hP
  exact tensor_commute P h.op _ hp (fun g =>
    commute_localUnit G R S.measurements P h.op g hp
      (axes_centralize G R S hS h hm P hP g)) i j

/-- In the common matrix-unit coordinates, every off-diagonal density block
vanishes and all diagonal blocks equal the same compressed density. This is
the algebraic form of h = I_(4^r) tensor h0 on the original support. -/
theorem common_density_blocks (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : Preliminaries.SupportOf h P)
    (o i j : Register (RowSlots.squares R)) :
    let t := tensorUnit P (localUnit G R S.measurements P)
    t o i*h.op*t j o=if i=j then h.op*t o o else 0 := by
  have ht := common_matrix_units G R S hS h hm P hP
  have hc := common_units_centralize G R S hS h hm P hP o i
  dsimp only
  rw [← hc.eq,mul_assoc,ht.1]
  split_ifs <;> simp

#print axioms common_matrix_units
#print axioms common_units_centralize
#print axioms common_density_blocks
end Sigma2.RowScalar
