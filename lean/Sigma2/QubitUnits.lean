import Sigma2.PauliMatrixUnits
noncomputable section
open scoped BigOperators
namespace Sigma2.QubitUnits
open PauliMatrixUnits

theorem projector_mulX (e X Z : Op) (h : Pair e X Z) (a : Fin 2) :
    projector e Z a*X=X*projector e Z (PauliMatrixUnits.flip a) := by
  rw [flip_projector e X Z h (PauliMatrixUnits.flip a),PauliMatrixUnits.flip_flip]

theorem p_xp (e X Z : Op) (h : Pair e X Z) (a b : Fin 2) :
    projector e Z a*(X*projector e Z b)=if PauliMatrixUnits.flip a=b then X*projector e Z b else 0 := by
  rw [← mul_assoc,projector_mulX e X Z h a,mul_assoc,projector_mul e X Z h]
  by_cases hab : PauliMatrixUnits.flip a=b
  · simp only [hab,ite_true]
  · simp only [hab,ite_false,mul_zero]

theorem xp_p (e X Z : Op) (h : Pair e X Z) (a b : Fin 2) :
    (X*projector e Z a)*projector e Z b=if a=b then X*projector e Z b else 0 := by
  rw [mul_assoc,projector_mul e X Z h]
  by_cases hab : a=b
  · simp only [hab,ite_true]
  · simp only [hab,ite_false,mul_zero]

theorem xp_xp (e X Z : Op) (h : Pair e X Z) (a b : Fin 2) :
    (X*projector e Z a)*(X*projector e Z b)=if PauliMatrixUnits.flip a=b then projector e Z b else 0 := by
  rw [mul_assoc,p_xp e X Z h]
  by_cases hab : PauliMatrixUnits.flip a=b
  · rw [if_pos hab,← mul_assoc,h.XX,(projector_supported e X Z h b).1,if_pos hab]
  · simp only [hab,ite_false,mul_zero]

theorem qubit_product (e X Z : Op) (h : Pair e X Z) (a b c d : Fin 2) :
    qubitUnit e X Z a b*qubitUnit e X Z c d=if b=c then qubitUnit e X Z a d else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [qubitUnit,projector_mul e X Z h,p_xp e X Z h,xp_p e X Z h,xp_xp e X Z h,PauliMatrixUnits.flip]

theorem qubit_star (e X Z : Op) (h : Pair e X Z) (a b : Fin 2) :
    star (qubitUnit e X Z a b)=qubitUnit e X Z b a := by
  fin_cases a <;> fin_cases b <;>
    norm_num [qubitUnit,star_mul,projector_star e X Z h,h.starX,projector_mulX e X Z h,PauliMatrixUnits.flip]

theorem qubit_diagonal (e X Z : Op) (a : Fin 2) : qubitUnit e X Z a a=projector e Z a := by simp [qubitUnit]

theorem qubit_sum (e X Z : Op) : ∑ a,qubitUnit e X Z a a=e := by
  simpa [qubit_diagonal,Fin.sum_univ_succ] using projector_sum e Z

#print axioms qubit_product
#print axioms qubit_star
end Sigma2.QubitUnits
