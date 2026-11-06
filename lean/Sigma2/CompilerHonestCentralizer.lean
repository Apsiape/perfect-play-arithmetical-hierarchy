import Sigma2.CompilerHonestFMSLift

/-! Every named honest projection centralizes the same actual marginal.
No commutation between distinct input labels is used. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestCentralizer
open Compiler CompilerScaffold CompilerFiniteRegister CompilerHonestDensity
  CompilerProjectionDictionary CompilerHonestPolynomial CompilerHonestQutrit
  CompilerHonestLift CompilerHonestFMSLift FiniteAncilla

 theorem central_star (h : Density) (A : Op) (hc : Centralizes h.op A) :
    Centralizes h.op (star A) := by
  have hh := congrArg (fun B : Op => star B) hc
  change h.op*star A=star A*h.op
  simpa only [star_mul,h.positive.isSelfAdjoint.star_eq] using hh.symm

/-- Uniform scalar weights allow all centralizing operator-valued blocks. -/
theorem uniform_matrix (d : ℕ) [NeZero d] (c : ℝ) (h : Density)
    (A : Matrix (Fin d) (Fin d) Op) (hc : ∀ i j,Centralizes h.op (A i j)) :
    Centralizes (weightedOp d (fun _ => c) h.op) (matrixOp d A) := by
  have he : diagonalBlocks d (fun _ => c) h.op=Matrix.diagonal (fun _ => (c:ℂ) • h.op) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i=j <;> simp [diagonalBlocks,Matrix.diagonal_apply,hij]
  change matrixOp d _*matrixOp d A=matrixOp d A*matrixOp d _
  rw [← matrixOp_mul,← matrixOp_mul,he]
  congr 1
  apply Matrix.ext
  intro i j
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal,smul_mul_assoc,mul_smul_comm,hc i j]

theorem qutrit_matrix (h : Density) (A : Matrix (Fin 3) (Fin 3) Op)
    (hc : ∀ i j,Centralizes (scaffoldDensity h).op (A i j)) :
    Centralizes (density h).op (matrixOp 3 A) :=
  uniform_matrix 3 (1/3) (scaffoldDensity h) A hc

theorem qutrit_amplify (h : Density) (A : Op)
    (hc : Centralizes (scaffoldDensity h).op A) :
    Centralizes (density h).op (amplify 3 A) := by
  dsimp only [Centralizes] at hc
  rw [← RowCompleteness.matrixOp_constantDiagonal]
  apply qutrit_matrix
  intro i j
  by_cases hij : i=j <;> simp [RowCompleteness.constantDiagonal,Matrix.diagonal_apply,hij,Centralizes,hc]

theorem qutrit_lift (h : Density) (a b : Fin 3) (A : Op)
    (hc : Centralizes (scaffoldDensity h).op A) :
    Centralizes (density h).op (lift 3 a b A) := by
  dsimp only [Centralizes] at hc
  apply qutrit_matrix
  intro i j
  by_cases hi : i=a <;> by_cases hj : j=b <;>
    simp [CompilerApproxBlocks.singleBlocks,hi,hj,Centralizes,hc]

theorem qutrit_pair (h : Density) (k : ℕ) (A : Op)
    (hc : Centralizes (density h).op A) : Centralizes (density h).op (inPair k A) := by
  have hp : Centralizes (density h).op (permutation 3 (pairPerm k)) :=
    permutation_centralizer 3 (fun _ => (1/3:ℝ)) (scaffoldDensity h).op _ (by intro i; rfl)
  exact ((show Commute _ _ from hp).mul_right hc).mul_right (central_star _ _ hp)

theorem graphPart_central (h : Density) (U : Op)
    (hc : Centralizes (scaffoldDensity h).op U) (part : ℕ) :
    Centralizes (density h).op (graphPart U part) := by
  have hcs := central_star (scaffoldDensity h) U hc
  dsimp only [Centralizes] at hc hcs
  unfold graphPart
  split_ifs
  all_goals apply qutrit_matrix
  all_goals intro i j; fin_cases i <;> fin_cases j
  all_goals simp [graphBlocks,calibratedBlocks,calibratedComplement,Centralizes,
    star_neg,smul_mul_assoc,mul_smul_comm,mul_neg,neg_mul,hc,hcs]
  all_goals first
    | exact ((show Commute (scaffoldDensity h).op U from hc).smul_right ((2:ℂ)⁻¹)).neg_right.eq
    | exact congrArg (fun A : Op => ((2:ℂ)⁻¹) • A)
        (central_star (scaffoldDensity h) (-U) (show Commute (scaffoldDensity h).op U from hc).neg_right.eq)

theorem projection_centralizer {P : Presentation} (R : StructuralRealization P) (n : ProjectionName) :
    Centralizes (density R.density).op (projection R n) := by
  have hu (w : Word) : Centralizes (scaffoldDensity R.density).op
      (evalWord (CompilerHonestDictionary.dictionary R) w) :=
    evalWord_centralizer _ _ (CompilerHonestDictionary.dictionary_centralizer R) w
  have hp (i : ℕ) := CompilerHonestDictionary.parameter_centralizer R.density i
  cases n with
  | parameter i => exact qutrit_amplify _ _ (hp i)
  | active g =>
      apply qutrit_amplify
      apply diagonal_centralizer
      intro i
      split_ifs <;> simp [Centralizes]
  | frame i => exact qutrit_lift _ _ _ _ (by simp [Centralizes])
  | graph w k part => exact qutrit_pair _ _ _ (graphPart_central _ _ (hu w) part)
  | triangle u v w =>
      apply qutrit_matrix
      have huc := hu u
      have hvc := hu v
      have hwc := (show Commute _ _ from huc).mul_right hvc
      have hus := central_star (scaffoldDensity R.density) _ huc
      have hvs := central_star (scaffoldDensity R.density) _ hvc
      have hws := central_star (scaffoldDensity R.density) _ hwc
      simp only [Centralizes,star_mul] at huc hvc hus hvs hws
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [triangleBlocks,Centralizes,smul_mul_assoc,mul_smul_comm,huc,hvc,hwc.eq,hus,hvs,hws]
  | binding p i complement =>
      apply qutrit_lift
      cases complement
      · exact hp p
      · exact (Commute.one_right _).sub_right (hp p)
  | joint p pair a b =>
      apply qutrit_pair
      apply qutrit_matrix
      have hpc := hp p
      have hqc := (Commute.one_right _).sub_right hpc
      intro i j
      fin_cases i <;> fin_cases j <;> simp only [jointBlocks]
      all_goals split_ifs <;>
        simp_all [Centralizes,smul_mul_assoc,mul_smul_comm,hqc.eq]

#print axioms projection_centralizer
end Sigma2.CompilerHonestCentralizer
