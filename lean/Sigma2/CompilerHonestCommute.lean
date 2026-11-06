import Sigma2.CompilerHonestMeasurements

/-! Separate honest refinement measurements. No two input labels are assumed
 to commute. The only joint measurement is with its own scalar FMS partition. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestCommute
open Compiler CompilerScaffold CompilerHonestFamilies CompilerHonestScalar
  CompilerFiniteRegister CompilerHonestDictionary CompilerProjectionDictionary
  CompilerHonestFMSLift FiniteAncilla RowCompleteness
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials CompilerScaffold.structuralPolynomials
  CompilerScaffold.applicationPolynomials

 theorem embed_zero_outside {n d : ℕ} (e : Fin n → Fin d)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin d)
    (h : (∀ a,i≠e a) ∨ (∀ a,j≠e a)) : embed e A i j=0 := by
  rcases h with h | h
  · simp [embed,Matrix.mul_apply,inclusion,h]
  · simp [embed,Matrix.mul_apply,inclusion,h]

 theorem position_active (g : Fin 4) (a : Fin 5) :
    bridgeActive g.val (position g a)=true := by
  fin_cases a
  · have hg := g.isLt
    simp [position,bridgeActive,selected,show g.val<5 by omega]
  all_goals
    simp [position,bridgeActive]
    omega

 theorem extended_cross_zero (g : Fin 4)
    (Q : Partition (Matrix (Fin 5) (Fin 5) ℂ) (Fin 6)) (hz : Q.effect 5=0)
    (a : Fin 6) (i j : Fin 17)
    (h : bridgeActive g.val i≠bridgeActive g.val j) :
    (extend (position g) (position_injective g) Q hz).effect a i j=0 := by
  have hi : (∀ b,i≠position g b) ∨ (∀ b,j≠position g b) := by
    by_cases hai : bridgeActive g.val i=true
    · right
      intro b he
      subst j
      exact h (hai.trans (position_active g b).symm)
    · left
      intro b he
      subst i
      exact hai (position_active g b)
  have hij : i≠j := by intro he; subst j; exact h rfl
  change (embed (position g) (Q.effect a)+(if a=5 then 1-embed (position g) 1 else 0)) i j=0
  split_ifs <;> simp [Matrix.add_apply,Matrix.sub_apply,embed_zero_outside _ _ _ _ hi,
    Matrix.one_apply,hij]

 theorem scalar_repeated_commute (g : Fin 4)
    (A : Matrix (Fin 17) (Fin 17) ℂ)
    (hz : ∀ i j,bridgeActive g.val i≠bridgeActive g.val j → A i j=0) (U : Op) :
    Commute (scalarOp 17 A) (repeated 17 (bridgeActive g.val) U) := by
  change matrixOp 17 (blocks 17 A 1)*matrixOp 17 (Matrix.diagonal _) =
    matrixOp 17 (Matrix.diagonal _)*matrixOp 17 (blocks 17 A 1)
  rw [← matrixOp_mul,← matrixOp_mul]
  congr 1
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases he : bridgeActive g.val i=bridgeActive g.val j
  · simp [blocks,he,smul_mul_assoc,mul_smul_comm]
  · change ((A i j) • (1:Op))*_= _*((A i j) • (1:Op))
    rw [hz i j he,zero_smul ℂ (1:Op),zero_mul,mul_zero]

 theorem fms_repeated_commute (g : Fin 4) (bob : Bool) (x : Fin 5) (a : Fin 6) (U : Op) :
    Commute (scalarOp 17 ((if bob then CompilerHonestFamilies.bob g x
      else CompilerHonestFamilies.alice g x).effect a))
      (repeated 17 (bridgeActive g.val) U) := by
  apply scalar_repeated_commute
  intro i j hij
  cases bob
  · exact extended_cross_zero g _ (by simp [CompilerHonestFMS.alicePartition,
      CompilerHonestFMS.alice,CompilerHonestFMS.rankOne,CompilerHonestFMS.aliceVector_inactive]) a i j hij
  · exact extended_cross_zero g _ (by simp [CompilerHonestFMS.bobPartition,
      CompilerHonestFMS.bob,CompilerHonestFMS.rankOne,CompilerHonestFMS.bobVector_inactive]) a i j hij

 theorem amplify_matrix_commute {d : ℕ} [NeZero d] (T : Op)
    (A : Matrix (Fin d) (Fin d) Op) (h : ∀ i j,Commute T (A i j)) :
    Commute (amplify d T) (matrixOp d A) := by
  rw [← matrixOp_constantDiagonal]
  change matrixOp d (Matrix.diagonal (fun _ => T))*matrixOp d A =
    matrixOp d A*matrixOp d (Matrix.diagonal (fun _ => T))
  rw [← matrixOp_mul,← matrixOp_mul]
  congr 1
  apply Matrix.ext
  intro i j
  simpa only [Matrix.diagonal_mul,Matrix.mul_diagonal] using (h i j).eq

 theorem scalar_amplify_commute {d : ℕ} [NeZero d]
    (T : Op) (A : Matrix (Fin d) (Fin d) ℂ) :
    Commute (amplify d T) (scalarOp d A) := by
  apply amplify_matrix_commute
  intro i j
  simp [blocks,Commute,SemiconjBy,mul_smul_comm,smul_mul_assoc]

 theorem eval_block {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (l : Fin (encodingCount P)) :
    evalWord (dictionary R) [(33+5*encodingCount P+g.val*encodingCount P+l.val,false)]=
      repeated 17 (bridgeActive g.val) (encoding R l.val) := by
  have hg := g.isLt
  have hl := l.isLt
  have hc : 0<encodingCount P := by omega
  have hn : 33+5*encodingCount P+g.val*encodingCount P+l.val<33+9*encodingCount P := by nlinarith
  have hdiv : (g.val*encodingCount P+l.val)/encodingCount P=g.val := by
    rw [Nat.mul_comm g.val,Nat.mul_add_div hc,Nat.div_eq_of_lt hl,Nat.add_zero]
  have hmod : (g.val*encodingCount P+l.val)%encodingCount P=l.val := by
    rw [Nat.mul_comm g.val,Nat.mul_add_mod,Nat.mod_eq_of_lt hl]
  change dictionary R (33+5*encodingCount P+g.val*encodingCount P+l.val)=_
  simp only [dictionary]
  rw [dif_neg (by omega),dif_neg (by omega),if_neg (by omega),if_pos hn]
  have he : 33+5*encodingCount P+g.val*encodingCount P+l.val-33-5*encodingCount P=
    g.val*encodingCount P+l.val := by omega
  simp only [he,hdiv,hmod]

#print axioms fms_repeated_commute
#print axioms eval_block
end Sigma2.CompilerHonestCommute
