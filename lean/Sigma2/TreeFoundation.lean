import Sigma2.TreeBasic

noncomputable section
open scoped BigOperators
namespace Sigma2.TreeFoundation

/-- Admissibility gives the actual root projection, including its range bound. -/
theorem root_projection {P} (hP : P.admissible) (R : NormalRealization P) :
    Projection (R.label P.root) := by
  obtain ⟨hi, ht⟩ := List.getElem?_eq_some_iff.mp hP.1
  simpa only [ht,TypedAt] using R.typed ⟨P.root, hi⟩

/-- Norm bound for an orthogonal projection, without a nonzero hypothesis. -/
theorem projection_norm_le (Q : Op) (hQ : Projection Q) : ‖Q‖ ≤ 1 := by
  have hh := CStarRing.norm_star_mul_self (x := Q)
  rw [hQ.1,hQ.2] at hh
  nlinarith [norm_nonneg Q]

theorem creation_norm_le {P} (R : NormalRealization P) (a : Fin 4) :
    ‖R.creation a‖ ≤ 1 := by
  have hh := CStarRing.norm_star_mul_self (x := R.creation a)
  rw [R.isometries a a,if_pos rfl] at hh
  have he := projection_norm_le R.support R.support_projection
  nlinarith [norm_nonneg (R.creation a)]

theorem density_support_right {P} (R : NormalRealization P) :
    R.density.op*R.support=R.density.op := by
  have hh := congrArg star R.density_supported
  simpa only [star_mul,R.support_projection.1,
    R.density.positive.isSelfAdjoint.star_eq] using hh

/-- A normal density cannot live entirely in a rootless four-ary summand.
This norm argument is independent of the complete Fock decomposition. -/
theorem root_nonzero {P} (R : NormalRealization P) : R.label P.root ≠ 0 := by
  intro hz
  have he : (∑ a, R.creation a*star (R.creation a))=R.support := by
    simpa only [hz,sub_zero] using R.ranges
  have hd : R.density.op=∑ a, (1/16:ℂ) •
      (R.creation a*R.density.op*star (R.creation a)) := by
    calc
      _ = R.density.op*R.support := (density_support_right R).symm
      _ = R.density.op*(∑ a, R.creation a*star (R.creation a)) := by rw [he]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [← mul_assoc,R.modular a,smul_mul_assoc]
  have hbound (a : Fin 4) :
      ‖(1/16:ℂ) • (R.creation a*R.density.op*star (R.creation a))‖ ≤
        (1/16:ℝ)*‖R.density.op‖ := by
    rw [norm_smul]
    have hn : ‖(1/16:ℂ)‖=(1/16:ℝ) := by norm_num
    rw [hn]
    gcongr
    calc
      _ ≤ (‖R.creation a‖*‖R.density.op‖)*‖star (R.creation a)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*‖R.density.op‖)*1 := by
        rw [norm_star (R.creation a)]
        gcongr <;> exact creation_norm_le R a
      _ = _ := by ring
  have hnorm : ‖R.density.op‖ ≤ (1/4:ℝ)*‖R.density.op‖ := by
    calc
      _ = ‖∑ a, (1/16:ℂ) • (R.creation a*R.density.op*star (R.creation a))‖ := congrArg norm hd
      _ ≤ ∑ a, ‖(1/16:ℂ) • (R.creation a*R.density.op*star (R.creation a))‖ := norm_sum_le _ _
      _ ≤ ∑ _a : Fin 4, (1/16:ℝ)*‖R.density.op‖ := Finset.sum_le_sum (fun a _ => hbound a)
      _ = _ := by simp; ring
  have hzero : R.density.op=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg R.density.op])
  have ht := R.density.trace_one
  simp [hzero,entry] at ht

/-- A supported unitary commuting with the creations also commutes with the root. -/
theorem unitary_commutes_root {P} (R : NormalRealization P) (T : Op)
    (hu : TypedAt R.support T .unitary)
    (hs : R.support*T=T ∧ T*R.support=T)
    (hc : ∀ a, T*R.creation a=R.creation a*T) :
    T*R.label P.root=R.label P.root*T := by
  have hca (a : Fin 4) : star T*R.creation a=R.creation a*star T := by
    calc
      _ = star T*R.creation a*R.support := by rw [mul_assoc,(R.creation_supported a).2]
      _ = star T*R.creation a*(T*star T) := by rw [hu.2]
      _ = star T*(R.creation a*T)*star T := by noncomm_ring
      _ = star T*(T*R.creation a)*star T := by rw [hc a]
      _ = (star T*T)*R.creation a*star T := by noncomm_ring
      _ = _ := by rw [hu.1,(R.creation_supported a).1]
  have hcs (a : Fin 4) : T*star (R.creation a)=star (R.creation a)*T := by
    have hh := congrArg star (hca a)
    simpa only [star_mul,star_star] using hh.symm
  have hh : T*(∑ a,R.creation a*star (R.creation a))=
      (∑ a,R.creation a*star (R.creation a))*T := by
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc,hc a,mul_assoc,hcs a,← mul_assoc]
  rw [R.ranges,mul_sub,sub_mul,hs.1,hs.2] at hh
  exact sub_right_inj.mp hh

/-- A nonzero root contains a nonzero finite density block. -/
theorem root_density_block {P} (hP : P.admissible) (R : NormalRealization P) :
    ∃ (μ : ℂ) (v : H), μ≠0 ∧ v≠0 ∧
      R.density.op v=μ • v ∧ R.label P.root v=v := by
  classical
  by_contra hn
  have hp := root_projection hP R
  have hz : R.label P.root*R.density.op=0 := by
    apply DensityContraction.ext_blocks R.density
    intro μ v
    have hv := v.property
    rw [Module.End.mem_eigenspace_iff] at hv
    change R.density.op v=μ • (v : H) at hv
    change R.label P.root (R.density.op v)=0
    rw [hv,map_smul]
    by_cases hμ : μ=0
    · simp [hμ]
    · have hpr : R.label P.root (v : H)=0 := by
        by_contra hne
        have he := DensitySpectral.block_invariant R.density (R.label P.root)
          (R.centralizer P.root) μ v v.property
        rw [Module.End.mem_eigenspace_iff] at he
        exact hn ⟨μ,R.label P.root v,hμ,hne,he,
          congrArg (fun T : Op => T v) hp.2⟩
      rw [hpr,smul_zero]
  have hz' : R.density.op*R.label P.root=0 := by
    have hh := congrArg star hz
    simpa only [star_mul,hp.1,R.density.positive.isSelfAdjoint.star_eq,star_zero Op] using hh
  have hpzero : R.label P.root=0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply R.faithful_on (R.label P.root v)
    · exact congrArg (fun T : Op => T v) (R.label_supported P.root).1
    · exact congrArg (fun T : Op => T v) hz'
  exact root_nonzero R hpzero

/-- Partial unitaries are injective on their support, without an ambient inverse. -/
theorem unitary_injective_on_support {P} (R : NormalRealization P) (T : Op)
    (hu : TypedAt R.support T .unitary) (v w : H)
    (hv : R.support v=v) (hw : R.support w=w) (he : T v=T w) : v=w := by
  have hh := congrArg (fun z : H => (star T : Op) z) he
  have hl (u : H) : star T (T u)=R.support u :=
    congrArg (fun A : Op => A u) hu.1
  simpa only [hl,hv,hw] using hh
#print axioms root_density_block
#print axioms unitary_injective_on_support
#print axioms root_projection
#print axioms creation_norm_le
#print axioms root_nonzero
#print axioms unitary_commutes_root
end Sigma2.TreeFoundation