import Sigma2.Compiler
import Sigma2.TableauProof
import Sigma2.FockEntropy

noncomputable section
open scoped BigOperators
namespace Sigma2.Tree

def fockWeight (w : Word) : ℝ := (3/4:ℝ)*(1/16:ℝ)^w.length

/-- Section 5.1, normality rules out a rootless summand; includes Eqs. (30)-(32). -/
theorem fock_decomposition {P} (hP : P.admissible) (R : NormalRealization P) :
    (∀ m, (trace (R.density.op*depthProjection R m)).re=(1/4:ℝ)^m) ∧
    (∀ v, Filter.Tendsto (fun m => depthProjection R m v) Filter.atTop (nhds 0)) ∧
    (∀ v, Summable (fun w : Word => wordProjection R w v)) ∧
    (∀ v, (∑' w : Word, wordProjection R w v)=R.support v) ∧
    (trace (R.density.op*R.label P.root)).re=3/4 ∧
    R.label P.root ≠ 0 := by
  exact ⟨depth_trace R,
    (fun v => by simpa only [depth_eq_tail] using TreeTail.strong_tail_zero R v),
    word_partition_summable hP R,word_partition hP R,
    FockTrace.root_mass hP R,TreeFoundation.root_nonzero R⟩

/-- Eq. (32), density transports down each Fock word by exactly 16^(-length). -/
theorem fock_density {P} (hP : P.admissible) (R : NormalRealization P) (w : Word) :
    R.density.op*wordOp R w*R.label P.root=
      ((1/16:ℂ)^w.length) • (wordOp R w*R.label P.root*R.density.op) := by
  have hw : wordOp R w=w.foldr (fun a A => R.creation a*A) R.support := by
    induction w with
    | nil => rfl
    | cons a w ih => simpa only [wordOp,List.foldr_cons,ih]
  have hh := TreeBasic.word_covariance R w
  rw [← hw] at hh
  have hc := R.centralizer P.root
  change R.density.op*R.label P.root=R.label P.root*R.density.op at hc
  rw [hh,smul_mul_assoc,mul_assoc,hc,← mul_assoc]

/-- Eq. (33), normalized Fock distribution and its finite entropy. -/
theorem fock_entropy : Summable fockWeight ∧ (∑' w, fockWeight w)=1 ∧
    Summable (fun w => entropyTerm (fockWeight w)) ∧
    (∑' w, entropyTerm (fockWeight w))=Real.log (4/3)/Real.log 2+4/3 := by
  have he : fockWeight=FockEntropy.weight := rfl
  rw [he]
  exact FockEntropy.result

/-- Lemma 5.1, Definite computation. No global commutation of update factors is assumed. -/
theorem lemma_5_1_definite_computation {P} (hP : P.admissible) (R : NormalRealization P)
    (C : Coordinates R) (M : Automaton) (T : Tableau R C M)
    (pulse : ℕ → Bool) (ξ : H) (hξ : R.label P.root ξ=ξ)
    (hp : ∀ w, T.pulse (wordOp R w ξ)=if pulse (yCoord w) then wordOp R w ξ else 0) :
    ∀ w c, T.symbol c (wordOp R w ξ)=
      if run M pulse (yCoord w) (xCoord w)=c then wordOp R w ξ else 0 := by
  exact definite_tableau hP R C M T pulse ξ hξ hp

/-- Section 5.1/7, finite-dimensional source supports cannot contain four isometries. -/
theorem no_finite_realization {P} (hP : P.admissible) (R : NormalRealization P) :
    ¬ FiniteRealization R := by
  exact TreeBasic.no_finite R

end Sigma2.Tree



