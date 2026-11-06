import Sigma2.TableauInduction

noncomputable section
open scoped BigOperators
namespace Sigma2.Tree

variable {P : Presentation} (hP : P.admissible) (R : NormalRealization P)
  (C : Coordinates R) (M : Automaton) (T : Tableau R C M)
  (pulse : ℕ → Bool) (ξ : H) (hξ : R.label P.root ξ=ξ)

include hP hξ in
theorem tableau_step (t : ℕ)
    (hp : ∀ w, T.pulse (wordOp R w ξ)=if pulse (yCoord w) then wordOp R w ξ else 0)
    (hr : ∀ u, yCoord u=t → ∀ c, T.symbol c (wordOp R u ξ)=
      if run M pulse t (xCoord u)=c then wordOp R u ξ else 0)
    (w : Word) (hy : yCoord w=t) (ht : t+1<2^w.length) (a : Symbol M) :
    T.symbol a (wordOp R (nextY w) ξ)=
      if run M pulse (t+1) (xCoord w)=a then wordOp R (nextY w) ξ else 0 := by
  let L := leftFactor R C M T
  let N := rightFactor R C M T
  let E : Bool → Op := fun ε => if ε then T.pulse else R.support-T.pulse
  have hE (ε : Bool) : E ε (wordOp R w ξ)=
      if pulse t=ε then wordOp R w ξ else 0 := by
    have hh := hp w
    rw [hy] at hh
    cases ε <;> cases he : pulse t <;>
      simp [E,he] at hh ⊢ <;> simp [hh,word_support_apply R ξ w]
  have hsum := ordered_update_sum M L T.symbol N E (wordOp R w ξ)
    (if xCoord w=0 then none else some (run M pulse t (xCoord w-1)))
    (run M pulse t (xCoord w)) (run M pulse t (xCoord w+1)) (pulse t)
    (left_factor_apply hP R C M T pulse ξ hξ t hr w hy)
    (hr w hy) (right_factor_apply hP R C M T pulse ξ hξ t hr w hy ht) hE a
  have hg : (R.support-star C.uy*C.py*C.uy) (wordOp R w ξ)=wordOp R w ξ := by
    rw [sub_apply,word_support_apply R ξ,last_y_apply hP R C ξ hξ,
      if_neg (by omega),sub_zero]
  have heq := congrArg (fun A : Op => A (wordOp R w ξ)) (T.transition a)
  change ((star C.uy*T.symbol a*C.uy-
    ∑ l,∑ c,∑ r,∑ ε : Bool,if M.update l c r ε=a then L l*T.symbol c*N r*E ε else 0)*
      (R.support-star C.uy*C.py*C.uy)) (wordOp R w ξ)=0 at heq
  rw [mul_apply_eq_comp,hg,sub_apply,hsum] at heq
  have ha : star C.uy (T.symbol a (wordOp R (nextY w) ξ))=
      if run M pulse (t+1) (xCoord w)=a then wordOp R w ξ else 0 := by
    convert sub_eq_zero.mp heq using 1 <;>
      simp only [mul_apply_eq_comp,(coordinate_identification hP R C w ξ hξ).2.1,run] <;> split_ifs <;> rfl
  calc
    _ = R.support (T.symbol a (wordOp R (nextY w) ξ)) :=
      (congrArg (fun A : Op => A (wordOp R (nextY w) ξ)) (T.supported.1 a).1).symm
    _ = C.uy (star C.uy (T.symbol a (wordOp R (nextY w) ξ))) :=
      (congrArg (fun A : Op => A (T.symbol a (wordOp R (nextY w) ξ))) C.uy_unitary.2).symm
    _ = _ := by
      rw [ha]
      split_ifs <;> simp only [map_zero,(coordinate_identification hP R C w ξ hξ).2.1]

include hP hξ in
theorem definite_tableau
    (hp : ∀ w, T.pulse (wordOp R w ξ)=if pulse (yCoord w) then wordOp R w ξ else 0) :
    ∀ w c, T.symbol c (wordOp R w ξ)=
      if run M pulse (yCoord w) (xCoord w)=c then wordOp R w ξ else 0 := by
  have rows : ∀ t w, yCoord w=t → ∀ c, T.symbol c (wordOp R w ξ)=
      if run M pulse t (xCoord w)=c then wordOp R w ξ else 0 := by
    intro t
    induction t with
    | zero =>
      intro w hy
      intro c
      convert initial_symbols hP R C M T ξ hξ w hy c using 1 <;> simp only [run] <;> split_ifs <;> rfl
    | succ t ih =>
      intro w hy c
      obtain ⟨u,hl,hx,hu,hn⟩ := previous_y w (by omega)
      have hut : yCoord u=t := by omega
      have hb := (coord_bounds w).2
      have ht : t+1<2^u.length := by rw [hl]; omega
      have hh := tableau_step hP R C M T pulse ξ hξ t hp ih u hut ht c
      simpa only [hn,hx] using hh
  intro w c
  exact rows (yCoord w) w rfl c

#print axioms definite_tableau
end Sigma2.Tree
