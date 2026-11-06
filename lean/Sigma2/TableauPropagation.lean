import Sigma2.TableauGeometry

noncomputable section
open scoped BigOperators
namespace Sigma2.Tree

variable {P : Presentation} (hP : P.admissible) (R : NormalRealization P)
  (C : Coordinates R) (M : Automaton) (T : Tableau R C M)
  (ξ : H) (hξ : R.label P.root ξ=ξ)

theorem word_support_apply (w : Word) : R.support (wordOp R w ξ)=wordOp R w ξ :=
  congrArg (fun A : Op => A ξ) (word_supported R w).1

include hP hξ in
theorem inverse_x_apply (w : Word) :
    star C.ux (wordOp R (nextX w) ξ)=wordOp R w ξ := by
  rw [← (coordinate_identification hP R C w ξ hξ).1]
  exact (congrArg (fun A : Op => A (wordOp R w ξ)) C.ux_unitary.1).trans
    (word_support_apply R ξ w)

include hP hξ in
theorem inverse_y_apply (w : Word) :
    star C.uy (wordOp R (nextY w) ξ)=wordOp R w ξ := by
  rw [← (coordinate_identification hP R C w ξ hξ).2.1]
  exact (congrArg (fun A : Op => A (wordOp R w ξ)) C.uy_unitary.1).trans
    (word_support_apply R ξ w)

include hP hξ in
theorem last_x_apply (w : Word) :
    (star C.ux*C.px*C.ux) (wordOp R w ξ)=
      if xCoord w+1=2^w.length then wordOp R w ξ else 0 := by
  simp only [mul_apply_eq_comp,(coordinate_identification hP R C w ξ hξ).1,
    (coordinate_identification hP R C (nextX w) ξ hξ).2.2.1]
  have hb := coord_bounds w
  have hg := (nextX_geometry w).2.1
  by_cases h : xCoord w+1=2^w.length
  · simp only [h,ite_true] at hg ⊢
    rw [hg,if_pos rfl,inverse_x_apply hP R C ξ hξ w]
  · simp only [h,ite_false] at hg ⊢
    rw [hg,if_neg (by omega),map_zero]

include hP hξ in
theorem last_y_apply (w : Word) :
    (star C.uy*C.py*C.uy) (wordOp R w ξ)=
      if yCoord w+1=2^w.length then wordOp R w ξ else 0 := by
  simp only [mul_apply_eq_comp,(coordinate_identification hP R C w ξ hξ).2.1,
    (coordinate_identification hP R C (nextY w) ξ hξ).2.2.2]
  have hb := coord_bounds w
  have hg := (nextY_geometry w).2.2
  by_cases h : yCoord w+1=2^w.length
  · simp only [h,ite_true] at hg ⊢
    rw [hg,if_pos rfl,inverse_y_apply hP R C ξ hξ w]
  · simp only [h,ite_false] at hg ⊢
    rw [hg,if_neg (by omega),map_zero]

theorem previous_x (w : Word) (hx : 0<xCoord w) :
    ∃ u : Word, u.length=w.length ∧ xCoord u=xCoord w-1 ∧
      yCoord u=yCoord w ∧ nextX u=w := by
  have hb := coord_bounds w
  obtain ⟨u,hl,hu,hv⟩ := word_of_coords w.length (xCoord w-1) (yCoord w) (by omega) hb.2
  refine ⟨u,hl,hu,hv,word_ext_coords _ _ ((nextX_geometry u).1.trans hl) ?_ (by simpa [hv] using (nextX_geometry u).2.2)⟩
  rw [(nextX_geometry u).2.1,hl,hu,if_neg (by omega)]
  omega

theorem previous_y (w : Word) (hy : 0<yCoord w) :
    ∃ u : Word, u.length=w.length ∧ xCoord u=xCoord w ∧
      yCoord u=yCoord w-1 ∧ nextY u=w := by
  have hb := coord_bounds w
  obtain ⟨u,hl,hu,hv⟩ := word_of_coords w.length (xCoord w) (yCoord w-1) hb.1 (by omega)
  refine ⟨u,hl,hu,hv,word_ext_coords _ _ ((nextY_geometry u).1.trans hl) (by simpa [hu] using (nextY_geometry u).2.1) ?_⟩
  rw [(nextY_geometry u).2.2,hl,hv,if_neg (by omega)]
  omega

theorem symbol_of_fixed (v : H) (c₀ : Symbol M) (hc₀ : T.symbol c₀ v=v) :
    ∀ c, T.symbol c v=if c₀=c then v else 0 := by
  intro c
  by_cases h : c₀=c
  · subst c; simpa using hc₀
  · rw [if_neg h,← hc₀]
    exact congrArg (fun A : Op => A v) (T.orthogonal c c₀ (Ne.symm h))

include hP hξ in
theorem initial_symbols (w : Word) (hy : yCoord w=0) :
    ∀ c, T.symbol c (wordOp R w ξ)=
      if run M (fun _ => false) 0 (xCoord w)=c then wordOp R w ξ else 0 := by
  have hp := (coordinate_identification hP R C w ξ hξ).2.2
  have hs := word_support_apply R ξ w
  have hpy : C.py (wordOp R w ξ)=wordOp R w ξ := by simpa [hy] using hp.2
  by_cases hx : xCoord w=0
  · have hpx : C.px (wordOp R w ξ)=wordOp R w ξ := by simpa [hx] using hp.1
    have hh := congrArg (fun A : Op => A (wordOp R w ξ)) T.initial_start
    simp only [mul_apply_eq_comp,hpx,hpy] at hh
    simpa [run,hx] using symbol_of_fixed R C M T (wordOp R w ξ) 0 hh
  · have hpx : C.px (wordOp R w ξ)=0 := by simpa [hx] using hp.1
    have hh := congrArg (fun A : Op => A (wordOp R w ξ)) T.initial_blank
    simp only [mul_apply_eq_comp,sub_apply,hpy,hpx,hs,sub_zero] at hh
    simpa [run,hx] using symbol_of_fixed R C M T (wordOp R w ξ) 1 hh

end Sigma2.Tree
