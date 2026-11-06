import Sigma2.RowSlotUnique
import Sigma2.RowColumns

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral FiniteJoint

/-- The two active scalar classes are precisely the actual canonical pair
answers 0 and 1. All nonzero cosets belong to class 2. -/
theorem slotSector_pair (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (j : ℕ) (c : Fin 2) :
    slotSector bob G R M P j c.val=pairJoint bob G R M P j c.val := by
  let a : Answer G R := ⟨c.val,by have := c.isLt; dsimp [Answer,AA,scenario]; omega⟩
  have he (b : Answer G R) : scalarClass b.val=c.val ↔ b=a := by
    rw [Fin.ext_iff]
    change scalarClass b.val=c.val ↔ b.val=c.val
    have hc := c.isLt
    unfold scalarClass
    split_ifs <;> omega
  simp only [slotSector,coarse,decide_eq_true_eq,he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

def sixAnswer (G : Game) (R : Rows G.scenario) (a : Fin 6) : Answer G R :=
  ⟨a.val,by have := a.isLt; dsimp [Answer,AA,scenario]; omega⟩

def boolNat (b : Bool) : ℕ := if b then 1 else 0

theorem boolNat_lt (b : Bool) : boolNat b<2 := by cases b <;> decide

/-- Coarse graph event selected by the actual column/slot forbidden-pair
rule. Its two terms correspond to the old bit 1 and the old bit 0. -/
def slotGraph (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (r : Fin R.rowCount)
    (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (eps : Bool) : Op :=
  let neg := (RowSlots.slot R r j).negative
  newEffects bob G R M P (slotQ R r j hj)
    (sixAnswer G R ⟨3+boolNat (Bool.xor eps neg),by have := boolNat_lt (Bool.xor eps neg); omega⟩) +
  newEffects bob G R M P (slotQ R r j hj)
    (sixAnswer G R ⟨boolNat (Bool.xor eps (!neg)),by have := boolNat_lt (Bool.xor eps (!neg)); omega⟩)

/-- The supported signed reflection; for deterministic slots this is ±P. -/
def slotReflection (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (r : Fin R.rowCount) (j : ℕ) : Op :=
  RowColumns.sign (RowSlots.slot R r j).negative •
    ((2:ℂ) • slotEvent bob G R M P r j-P)

private theorem graph_algebra (P E F0 F1 : Op) (h0 : P*F0=F0) (h1 : P*F1=F1)
    (neg eps : Bool) :
    E*(if Bool.xor eps neg then F1 else F0) +
      (P-E)*(if Bool.xor eps (!neg) then F1 else F0)=
      (1/2:ℂ) • ((F0+F1)+RowColumns.sign eps •
        ((RowColumns.sign neg • ((2:ℂ) • E-P))*(F0-F1))) := by
  cases neg <;> cases eps <;> norm_num [RowColumns.sign,Bool.xor]
  all_goals simp only [sub_mul,mul_sub,smul_mul_assoc,neg_mul,h0,h1]
  all_goals module
theorem new_fine_supported (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (hP : Projection P)
    (q : NewQ R) (a : Answer G R) :
    P*newEffects bob G R M P q a=newEffects bob G R M P q a ∧
      newEffects bob G R M P q a*P=newEffects bob G R M P q a := by
  cases bob <;> simp only [newEffects,compressed,Bool.false_eq_true,ite_false,ite_true]
  all_goals exact ⟨by simp only [← mul_assoc,hP.2],by simp only [mul_assoc,hP.2]⟩

/-- Both signs of every actual signed slot graph, as two-coordinate spectral
blocks. D is the scalar {0,j} sector and K its signed pair transition.
No commutation of different row reflections is assumed. -/
theorem slot_graph_formula (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (eps : Bool) :
    let F0 := pairJoint bob G R S.measurements P j 0
    let F1 := pairJoint bob G R S.measurements P j 1
    slotGraph bob G R S.measurements P r j hj eps=
      (1/2:ℂ) • ((F0+F1)+RowColumns.sign eps •
        (slotReflection bob G R S.measurements P r j*(F0-F1))) := by
  dsimp only
  let neg := (RowSlots.slot R r j).negative
  have he (c : Bool) : slotSector bob G R S.measurements P j (boolNat c)=
      if c then pairJoint bob G R S.measurements P j 1
        else pairJoint bob G R S.measurements P j 0 := by
    cases c
    · exact slotSector_pair bob G R S.measurements P j ⟨0,by decide⟩
    · exact slotSector_pair bob G R S.measurements P j ⟨1,by decide⟩
  have ha (c : Bool) :
      (3+boolNat c)/3=1 ∧ (3+boolNat c)%3=boolNat c ∧
      boolNat c/3=0 ∧ boolNat c%3=boolNat c := by cases c <;> decide
  have hp (c : Fin 2) : P*pairJoint bob G R S.measurements P j c.val=
      pairJoint bob G R S.measurements P j c.val := by
    let a := sixAnswer G R ⟨c.val,by have := c.isLt; omega⟩
    have hh := pair_unique bob G R S hS h hm P hP j hj a
    change newEffects bob G R S.measurements P (pairQ R j hj) a=pairJoint bob G R S.measurements P j c.val at hh
    rw [← hh]
    exact (new_fine_supported bob G R S.measurements P hP.1 _ a).1
  have hfirst (c : Bool) :
      newEffects bob G R S.measurements P (slotQ R r j hj)
        (sixAnswer G R ⟨3+boolNat c,by have := boolNat_lt c; omega⟩)=
      slotEvent bob G R S.measurements P r j *
        (if c then pairJoint bob G R S.measurements P j 1 else pairJoint bob G R S.measurements P j 0) := by
    have hh := slot_unique bob G R S hS h hm P hP r j hj
      (sixAnswer G R ⟨3+boolNat c,by have := boolNat_lt c; omega⟩)
    have hc : 3+boolNat c<6 := by have := boolNat_lt c; omega
    simpa only [sixAnswer,hc,ite_true,(ha c).1,(ha c).2.1,he c] using hh
  have hsecond (c : Bool) :
      newEffects bob G R S.measurements P (slotQ R r j hj)
        (sixAnswer G R ⟨boolNat c,by have := boolNat_lt c; omega⟩)=
      (P-slotEvent bob G R S.measurements P r j) *
        (if c then pairJoint bob G R S.measurements P j 1 else pairJoint bob G R S.measurements P j 0) := by
    have hh := slot_unique bob G R S hS h hm P hP r j hj
      (sixAnswer G R ⟨boolNat c,by have := boolNat_lt c; omega⟩)
    have hc : boolNat c<6 := by have := boolNat_lt c; omega
    simpa only [sixAnswer,hc,ite_true,(ha c).2.2.1,(ha c).2.2.2,
      show ¬(0:ℕ)=1 from by decide,ite_false,he c] using hh
  exact (congrArg₂ (fun A B : Op => A+B) (hfirst (Bool.xor eps neg))
    (hsecond (Bool.xor eps (!neg)))).trans
      (graph_algebra P (slotEvent bob G R S.measurements P r j) _ _
        (hp ⟨0,by decide⟩) (hp ⟨1,by decide⟩) neg eps)
/-- The scalar support of the graph block is exactly the two-coordinate
Z sector {0,j}, as opposed to a larger unidentified syndrome space. -/
theorem pair_active_sector (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) :
    pairJoint bob G R S.measurements P j 0+pairJoint bob G R S.measurements P j 1=
      coarse (newEffects bob G R S.measurements P (globalQ R false))
        (fun b => decide (b.val=0 ∨ b.val=j)) true := by
  let a0 := sixAnswer G R 0
  let a1 := sixAnswer G R 1
  have h0 := pair_coset_formula bob G R S hS h hm P hP j hj a0 (by
    have := RowSlots.dimension_pos R; simp [a0,sixAnswer,valid]; omega)
  have h1 := pair_coset_formula bob G R S hS h hm P hP j hj a1 (by
    have := RowSlots.dimension_pos R; simp [a1,sixAnswer,valid]; omega)
  rw [pair_unique bob G R S hS h hm P hP] at h0 h1
  simp only [a0,a1,sixAnswer,Fin.val_zero,Fin.val_one,Nat.zero_mod,Nat.zero_div,
    Nat.reduceMod,Nat.reduceDiv,Nat.xor_eq,Nat.zero_xor,
    show decide ((0:ℕ)=1)=false from rfl,decide_true] at h0 h1
  rw [h0,h1,← add_mul]
  have hs := (coarse_sum (newEffects bob G R S.measurements P (globalQ R true))
    (fun b => parity (2*RowSlots.squares R) j b.val)).trans
      (new_sum bob G R S.measurements P hP.1 _)
  rw [show _+_=P from (by simpa only [Fintype.sum_bool,add_comm] using hs)]
  exact (new_coarse_supported bob G R S.measurements P hP.1 _ _ true).1

#print axioms slotSector_pair
#print axioms boolNat_lt
#print axioms graph_algebra
#print axioms new_fine_supported
#print axioms slot_graph_formula
#print axioms pair_active_sector
end Sigma2.RowScalar



