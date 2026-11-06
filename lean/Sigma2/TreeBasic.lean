import Sigma2.CompilerBase

noncomputable section
open scoped BigOperators
namespace Sigma2.TreeBasic

/-- The exact modular covariance for any finite creation word. -/
theorem word_covariance {P} (R : NormalRealization P) :
    ∀ w : List (Fin 4),
      let A := w.foldr (fun a A => R.creation a*A) R.support
      R.density.op*A=((1/16:ℂ)^w.length) • (A*R.density.op) := by
  intro w
  induction w with
  | nil =>
    have hr : R.density.op*R.support=R.density.op := by
      have hh := congrArg star R.density_supported
      simpa only [star_mul,R.support_projection.1,R.density.positive.isSelfAdjoint.star_eq] using hh
    simpa only [List.foldr_nil,List.length_nil,pow_zero,one_smul,
      R.density_supported] using hr
  | cons a w ih =>
    dsimp only [List.foldr_cons,List.length_cons]
    rw [← mul_assoc,R.modular a,smul_mul_assoc,mul_assoc,ih,mul_smul_comm,smul_smul,
      pow_succ, mul_comm ((1/16:ℂ)^w.length) (1/16:ℂ),mul_assoc]

/-- Two orthogonal copies of a nonzero finite-dimensional support cannot each
be isometric images of the whole support. -/
theorem no_finite {P} (R : NormalRealization P) : ¬ FiniteRealization R := by
  intro hfin
  let S := LinearMap.range R.support.toLinearMap
  letI : FiniteDimensional ℂ S := hfin
  have hfix (v : S) : R.support v=v := by
    obtain ⟨w,hw⟩ := v.property
    change R.support w=(v : H) at hw
    rw [← hw]
    exact congrArg (fun A : Op => A w) R.support_projection.2
  have hmem (a : Fin 4) (v : H) : R.creation a v ∈ S := by
    refine ⟨R.creation a v,?_⟩
    exact congrArg (fun A : Op => A v) (R.creation_supported a).1
  let A (a : Fin 4) : S →ₗ[ℂ] S :=
    ((R.creation a).toLinearMap.domRestrict S).codRestrict S (fun v => hmem a v)
  have hleft (a : Fin 4) (v : S) : star (R.creation a) (A a v : H)=(v : H) := by
    have hh := congrArg (fun B : Op => B v) (R.isometries a a)
    change star (R.creation a) (R.creation a v)=(v : H)
    simpa only [ite_true,mul_apply_eq_comp,hfix] using hh
  have hinj (a : Fin 4) : Function.Injective (A a) := by
    intro v w he
    apply Subtype.ext
    have hh := congrArg (fun z : S => star (R.creation a) z) he
    simpa only [hleft] using hh
  have hsurj : Function.Surjective (A 0) := LinearMap.surjective_of_injective (hinj 0)
  have hzero (v : S) : (v : H)=0 := by
    obtain ⟨w,hw⟩ := hsurj (A 1 v)
    have he : (w : H)=0 := by
      rw [← hleft 0 w,hw]
      have hh := congrArg (fun B : Op => B v) (R.isometries 0 1)
      change star (R.creation 0) (R.creation 1 v)=0
      simpa only [show (0:Fin 4)≠1 by decide,ite_false,mul_apply_eq_comp,
        zero_apply] using hh
    have ha : (A 1 v : H)=0 := by
      rw [← hw]
      change R.creation 0 w=0
      rw [he,map_zero]
    rw [← hleft 1 v,ha,map_zero]
  have hs : R.support=0 := by
    apply ContinuousLinearMap.ext
    intro v
    exact hzero ⟨R.support v,⟨v,rfl⟩⟩
  have hd : R.density.op=0 := by simpa only [hs,zero_mul] using R.density_supported.symm
  have ht := R.density.trace_one
  simp [hd,entry] at ht

#print axioms word_covariance
#print axioms no_finite
end Sigma2.TreeBasic
