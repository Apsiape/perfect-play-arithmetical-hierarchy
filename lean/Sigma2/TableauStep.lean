import Sigma2.TableauPropagation

noncomputable section
open scoped BigOperators
namespace Sigma2.Tree

variable {P : Presentation} (hP : P.admissible) (R : NormalRealization P)
  (C : Coordinates R) (M : Automaton) (T : Tableau R C M)
  (pulse : ℕ → Bool) (ξ : H) (hξ : R.label P.root ξ=ξ)

def leftFactor (l : Option (Symbol M)) : Op := match l with
  | none => C.px
  | some c => C.ux*T.symbol c*star C.ux*(R.support-C.px)

def rightFactor (r : Symbol M) : Op :=
  star C.ux*T.symbol r*C.ux*(R.support-star C.ux*C.px*C.ux)+
    (if r=1 then star C.ux*C.px*C.ux else 0)

include hP hξ in
theorem left_factor_apply (t : ℕ)
    (hr : ∀ u, yCoord u=t → ∀ c, T.symbol c (wordOp R u ξ)=
      if run M pulse t (xCoord u)=c then wordOp R u ξ else 0)
    (w : Word) (hy : yCoord w=t) (l : Option (Symbol M)) :
    leftFactor R C M T l (wordOp R w ξ)=
      if (if xCoord w=0 then none else some (run M pulse t (xCoord w-1)))=l
      then wordOp R w ξ else 0 := by
  have hpx := (coordinate_identification hP R C w ξ hξ).2.2.1
  have hs := word_support_apply R ξ w
  cases l with
  | none => simpa [leftFactor] using hpx
  | some c =>
    by_cases hx : xCoord w=0
    · simp [leftFactor,mul_apply_eq_comp,sub_apply,hpx,hx,hs]
    · obtain ⟨u,hl,hu,hv,hn⟩ := previous_x w (by omega)
      have hi : star C.ux (wordOp R w ξ)=wordOp R u ξ := by
        rw [← hn,inverse_x_apply hP R C ξ hξ]
      simp only [leftFactor,mul_apply_eq_comp,sub_apply,hs,hpx,if_neg hx,sub_zero,
        hi,hr u (hv.trans hy),hu]
      simp only [Option.some.injEq]
      split_ifs <;> simp only [map_zero,(coordinate_identification hP R C u ξ hξ).1,hn]

include hP hξ in
theorem right_factor_apply (t : ℕ)
    (hr : ∀ u, yCoord u=t → ∀ c, T.symbol c (wordOp R u ξ)=
      if run M pulse t (xCoord u)=c then wordOp R u ξ else 0)
    (w : Word) (hy : yCoord w=t) (ht : t+1<2^w.length) (r : Symbol M) :
    rightFactor R C M T r (wordOp R w ξ)=
      if run M pulse t (xCoord w+1)=r then wordOp R w ξ else 0 := by
  have hg : (R.support-star C.ux*C.px*C.ux) (wordOp R w ξ)=
      if xCoord w+1=2^w.length then 0 else wordOp R w ξ := by
    rw [sub_apply,word_support_apply R ξ,last_x_apply hP R C ξ hξ]
    split_ifs <;> simp
  by_cases hx : xCoord w+1=2^w.length
  · have hb : run M pulse t (xCoord w+1)=1 := run_blank M pulse t _ (by omega)
    have hz : ((if r=1 then star C.ux*C.px*C.ux else 0) : Op) (wordOp R w ξ)=
        if (1 : Symbol M)=r then wordOp R w ξ else 0 := by
      by_cases hr₁ : r=1
      · rw [if_pos hr₁,last_x_apply hP R C ξ hξ,if_pos hx,if_pos hr₁.symm]
      · rw [if_neg hr₁,zero_apply,if_neg (Ne.symm hr₁)]
    simpa only [rightFactor,add_apply,mul_apply_eq_comp,hg,if_pos hx,map_zero,
      zero_add,hb] using hz
  · have hn : xCoord (nextX w)=xCoord w+1 := by
      rw [(nextX_geometry w).2.1,if_neg hx]
    have hlast : (star C.ux*C.px*C.ux) (wordOp R w ξ)=0 := by
      rw [last_x_apply hP R C ξ hξ,if_neg hx]
    simp only [rightFactor,add_apply,mul_apply_eq_comp,hg,if_neg hx,
      (coordinate_identification hP R C w ξ hξ).1,
      hr (nextX w) ((nextX_geometry w).2.2.trans hy),hn]
    have hz : ((if r=1 then star C.ux*C.px*C.ux else 0) : Op) (wordOp R w ξ)=0 := by
      split_ifs <;> simp_all
    rw [hz,add_zero]
    split_ifs <;> simp [inverse_x_apply hP R C ξ hξ]

end Sigma2.Tree
