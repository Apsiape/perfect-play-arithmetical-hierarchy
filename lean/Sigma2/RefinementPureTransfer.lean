import Sigma2.CalibrationEvents
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.RefinementPureTransfer
open Compiler Coefficients TensorLifts Purification PureTransfer

theorem slices_ext (v w : AB) (he : ∀ k,slice v k=slice w k) : v=w := by
  ext ⟨a,b⟩
  obtain ⟨⟨k,i⟩,ha⟩ := Nat.pairEquiv.surjective a
  subst a
  exact congrArg (fun z : AB => z (i,b)) (he k)

theorem preserving_bob_with_mirrors {s} (S : NormalStrategy s) :
    ∃ T : PureStrategy s,
      T.measurements=measurements S.measurements ∧
      (∀ h : Density,MarginalB S h → MarginalB (normalOfPure T) h) ∧
      (∀ x y a b,S.probability x y a b=T.probability x y a b) ∧
      (∀ x y a b,(∀ k,0<S.weight k → S.measurements.left x a (S.vector k)=
        S.measurements.right y b (S.vector k)) →
        T.measurements.left x a T.vector=T.measurements.right y b T.vector) := by
  let u : ℕ → AB := fun k => (Real.sqrt (S.weight k):ℂ) • S.vector k
  have hnorm k : ‖u k‖^2=S.weight k :=
    weighted_unit_norm _ (S.weight_nonneg k) _ (S.unit k)
  have hu : Summable (fun k => ‖u k‖^2) := by
    simpa only [hnorm] using S.weight_summable
  let Ω := pack u hu
  have hΩ : ‖Ω‖=1 := by
    have hh := pack_norm_sq u hu
    simp only [hnorm,S.weight_sum] at hh
    change ‖Ω‖^2=1 at hh
    nlinarith [norm_nonneg Ω]
  let T : PureStrategy s := ⟨measurements S.measurements,Ω,hΩ⟩
  refine ⟨T,rfl,?_,?_,?_⟩
  · intro h hm
    apply (marginalB_pure T h).mpr
    intro i j
    exact (hm i j).trans (pack_bob_entries S u hu (fun _ => rfl) i j).symm
  · intro x y a b
    change _=(inner ℂ Ω (((measurements S.measurements).left x a*
      (measurements S.measurements).right y b) Ω)).re
    rw [inner_slices]
    have hs := inner_slices_summable Ω
      (((measurements S.measurements).left x a*(measurements S.measurements).right y b) Ω)
    change _=Complex.reCLM (∑' k,inner ℂ (slice Ω k)
      (slice (((measurements S.measurements).left x a*
        (measurements S.measurements).right y b) Ω) k))
    rw [Complex.reCLM.map_tsum hs]
    apply tsum_congr
    intro k
    rw [slice_joint]
    dsimp only [Ω]
    rw [slice_pack]
    change S.weight k*(S.component k).probability x y a b=
      (inner ℂ (u k) ((S.measurements.left x a*S.measurements.right y b) (u k))).re
    rw [weighted_expectation _ (S.weight_nonneg k)]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl
  · intro x y a b hmirror
    apply slices_ext
    intro k
    change slice (left (amplify (S.measurements.alice x a)) Ω) k=
      slice (right (S.measurements.bob y b) Ω) k
    rw [slice_left,slice_right,slice_pack]
    by_cases hk : S.weight k=0
    · simp [u,hk]
    · have hp : 0<S.weight k := lt_of_le_of_ne (S.weight_nonneg k) (Ne.symm hk)
      have hh := hmirror k hp
      rw [measurements_left,measurements_right] at hh
      dsimp only [u]
      rw [map_smul,map_smul,hh]

theorem preserving_alice_with_mirrors {s} (S : NormalStrategy s) :
    ∃ T : PureStrategy s,
      T.measurements.alice=S.measurements.alice ∧
      T.measurements.bob=(fun y b => Purification.amplify (S.measurements.bob y b)) ∧
      (∀ h : Density,MarginalA S h → MarginalA (normalOfPure T) h) ∧
      (∀ x y a b,S.probability x y a b=T.probability x y a b) ∧
      (∀ x y a b,(∀ k,0<S.weight k → S.measurements.left x a (S.vector k)=
        S.measurements.right y b (S.vector k)) →
        T.measurements.left x a T.vector=T.measurements.right y b T.vector) := by
  obtain ⟨U,hU,hm,hp,hmir⟩ := preserving_bob_with_mirrors (flipNormal S)
  let T : PureStrategy s := flipPure U
  refine ⟨T,?_,?_,?_,?_,?_⟩
  · change U.measurements.bob=S.measurements.alice
    rw [hU]
    rfl
  · change U.measurements.alice=(fun y b => Purification.amplify (S.measurements.bob y b))
    rw [hU]
    rfl
  · intro h hh
    change MarginalB (normalOfPure U) h
    apply hm h
    exact hh
  · intro x y a b
    calc
      S.probability x y a b=(flipNormal S).probability y x b a :=
        (flipNormal_probability S x y a b).symm
      _ = U.probability y x b a := hp y x b a
      _ = T.probability x y a b := (flipPure_probability U y x b a).symm

  · intro x y a b hmirror
    have hf : ∀ k,0<(flipNormal S).weight k →
        (flipNormal S).measurements.left y b ((flipNormal S).vector k)=
          (flipNormal S).measurements.right x a ((flipNormal S).vector k) := by
      intro k hk
      have hh := hmirror k hk
      rw [measurements_left,measurements_right] at hh
      have hz := congrArg swap hh
      rw [swap_left,swap_right] at hz
      exact hz.symm
    have hh := hmir y x b a hf
    have hl := congrArg (fun L : BipOp => L U.vector) (measurements_left U.measurements y b)
    have hr := congrArg (fun L : BipOp => L U.vector) (measurements_right U.measurements x a)
    have hz := congrArg swap (hl.symm.trans (hh.trans hr))
    rw [swap_left,swap_right] at hz
    exact hz.symm

#print axioms preserving_bob_with_mirrors
#print axioms preserving_alice_with_mirrors
end Sigma2.RefinementPureTransfer
