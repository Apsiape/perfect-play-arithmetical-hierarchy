import Sigma2.DensityContraction
import Sigma2.CompilerBase

/-! Support-aware finite-eigenspace unitary completions for the honest compiler.
The zero-density eigenspace is handled explicitly, without a finite-dimensionality
or global-faithfulness assumption on that eigenspace. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerHonestEncoding
open DensitySpectral DensityContraction

/-- A centralizing contraction that vanishes on the density kernel is an exact
mean of density-centralizing ambient unitaries, with specified kernel actions. -/
theorem mean_with_kernel (h : Density) (T : Op) (hT : Contraction T)
    (hc : Centralizes h.op T) (hz : ∀ v, h.op v=0 → T v=0) :
    ∃ U V : Op, Unitary U ∧ Unitary V ∧
      Centralizes h.op U ∧ Centralizes h.op V ∧
      T=(1/2:ℂ) • (U+V) ∧
      (∀ v, h.op v=0 → U v=v ∧ V v= -v) := by
  letI (μ : ℂ) : CompleteSpace (block h μ) :=
    (ContinuousLinearMap.isClosed_eigenspace h.op μ).completeSpace_coe
  let Tμ (μ : ℂ) : block h μ →L[ℂ] block h μ :=
    T.restrict (fun v hv => block_invariant h T hc μ v hv)
  have hn (μ : ℂ) : ‖Tμ μ‖ ≤ 1 := by
    apply (Tμ μ).opNorm_le_bound (by norm_num)
    intro v
    change ‖T v‖ ≤ 1*‖(v : H)‖
    exact (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg v))
  have hm (μ : ℂ) : ∃ U V : unitary (block h μ →L[ℂ] block h μ),
      Tμ μ=(1/2:ℂ) • ((U : block h μ →L[ℂ] block h μ)+V) ∧
      (μ=0 → ∀ v : block h μ,
        (U : block h μ →L[ℂ] block h μ) v=v ∧
        (V : block h μ →L[ℂ] block h μ) v= -v) := by
    letI : CompleteSpace (block h μ) :=
      (ContinuousLinearMap.isClosed_eigenspace h.op μ).completeSpace_coe
    by_cases hμ : μ=0
    · have ht : Tμ μ=0 := by
        ext v : 1
        apply Subtype.ext
        change T v=0
        apply hz
        have hv := v.property
        rw [Module.End.mem_eigenspace_iff] at hv
        change h.op v=μ • (v:H) at hv
        simpa [hμ] using hv
      let V : unitary (block h μ →L[ℂ] block h μ) :=
        ⟨-1,by
          change star (-1 : block h μ →L[ℂ] block h μ)*(-1)=1 ∧
            (-1 : block h μ →L[ℂ] block h μ)*star (-1)=1
          have hs : star (-1 : block h μ →L[ℂ] block h μ)= -1 := by
            change ContinuousLinearMap.adjoint (-1 : block h μ →L[ℂ] block h μ)= -1
            rw [map_neg,ContinuousLinearMap.adjoint_one]
          constructor <;> rw [hs]
          all_goals
            ext v : 1
            change -(-v)=v
            exact neg_neg v⟩
      refine ⟨1,V,?_,?_⟩
      · rw [ht]
        change (0 : block h μ →L[ℂ] block h μ)=(1/2:ℂ) • (1+ -1)
        module
      · intro _ v
        exact ⟨rfl,rfl⟩
    · letI := finite_block h μ hμ
      obtain ⟨U,V,he⟩ := FiniteContraction.finite_mean (Tμ μ) (hn μ)
      exact ⟨U,V,he,fun heq => (hμ heq).elim⟩
  choose Uμ Vμ hμ using hm
  obtain ⟨U,hU⟩ := assemble h (fun μ => unitaryEquiv (Uμ μ))
  obtain ⟨V,hV⟩ := assemble h (fun μ => unitaryEquiv (Vμ μ))
  let A := U.toLinearIsometry.toContinuousLinearMap
  let B := V.toLinearIsometry.toContinuousLinearMap
  have ha : A ∈ unitary Op := FiniteContraction.isometry_unitary _ U.surjective
  have hb : B ∈ unitary Op := FiniteContraction.isometry_unitary _ V.surjective
  have hA (μ : ℂ) (v : block h μ) :
      A v=((Uμ μ : block h μ →L[ℂ] block h μ) v : H) := hU μ v
  have hB (μ : ℂ) (v : block h μ) :
      B v=((Vμ μ : block h μ →L[ℂ] block h μ) v : H) := hV μ v
  refine ⟨A,B,ha,hb,?_,?_,?_,?_⟩
  · apply centralizes_of_blocks
    intro μ v
    rw [hA]
    exact ((Uμ μ : block h μ →L[ℂ] block h μ) v).property
  · apply centralizes_of_blocks
    intro μ v
    rw [hB]
    exact ((Vμ μ : block h μ →L[ℂ] block h μ) v).property
  · apply ext_blocks h
    intro μ v
    have he := congrArg (fun C : block h μ →L[ℂ] block h μ => (C v : H)) (hμ μ).1
    change T v=(1/2:ℂ) • (A v+B v)
    rw [hA,hB]
    exact he
  · intro v hv
    let w : block h 0 := ⟨v,by
      rw [Module.End.mem_eigenspace_iff]
      change h.op v=(0:ℂ) • v
      simpa using hv⟩
    have he := (hμ 0).2 rfl w
    exact ⟨(hA 0 w).trans (congrArg Subtype.val he.1),
      (hB 0 w).trans (congrArg Subtype.val he.2)⟩

/-- Faithfulness on the actual support identifies the entire kernel summand;
no ambient faithfulness of a realization density is required. -/
theorem supported_kernel_zero (h : Density) (e T : Op)
    (he : Preliminaries.SupportOf h e) (hTe : T*e=T) :
    ∀ v, h.op v=0 → T v=0 := by
  have hre : h.op*e=h.op := by
    have hs := congrArg (fun A : Op => star A) he.2.1
    simpa only [star_mul,he.1.1,h.positive.isSelfAdjoint.star_eq] using hs
  intro v hv
  have hev : e (e v)=e v := congrArg (fun A : Op => A v) he.1.2
  have hhv : h.op (e v)=0 := by
    calc
      _=(h.op*e) v := rfl
      _=h.op v := congrArg (fun A : Op => A v) hre
      _=0 := hv
  have hz : e v=0 := he.2.2 _ hev hhv
  calc
    T v=(T*e) v := congrArg (fun A : Op => A v) hTe.symm
    _=T (e v) := rfl
    _=0 := by rw [hz,map_zero]

/-- The two-unitary completion is available directly for every supported
centralizer contraction in the frozen realization interface. -/
theorem supported_mean (h : Density) (e T : Op)
    (he : Preliminaries.SupportOf h e) (hT : Contraction T)
    (hc : Centralizes h.op T) (hTe : T*e=T) :
    ∃ U V : Op, Unitary U ∧ Unitary V ∧
      Centralizes h.op U ∧ Centralizes h.op V ∧
      T=(1/2:ℂ) • (U+V) ∧
      (∀ v, h.op v=0 → U v=v ∧ V v= -v) :=
  mean_with_kernel h T hT hc (supported_kernel_zero h e T he hTe)


/-- Both encoding unitaries can be made equal to the identity outside the
support. Their mean is the contraction completed by that identity, exactly the
`copyAtom` support convention in the frozen scaffold. -/
theorem supported_identity_mean (h : Density) (e T : Op)
    (he : Preliminaries.SupportOf h e) (hT : Contraction T)
    (hc : Centralizes h.op T) (hTe : T*e=T) :
    ∃ U V : Op, Unitary U ∧ Unitary V ∧
      Centralizes h.op U ∧ Centralizes h.op V ∧
      T+(1-e)=(1/2:ℂ) • (U+V) ∧
      (U-1)*(1-e)=0 ∧ (V-1)*(1-e)=0 := by
  obtain ⟨U,V,hU,hV,hcU,hcV,hm,hker⟩ := supported_mean h e T he hT hc hTe
  let Q : Op := 1-e
  have hQ : Projection Q := Compiler.projection_compl e he.1
  have hre : h.op*e=h.op := by
    have hs := congrArg (fun A : Op => star A) he.2.1
    simpa only [star_mul,he.1.1,h.positive.isSelfAdjoint.star_eq] using hs
  have hqzero : h.op*Q=0 := by dsimp [Q]; rw [mul_sub,mul_one,hre,sub_self]
  have hUQ : U*Q=Q := by
    ext v : 1
    exact (hker (Q v) (congrArg (fun A : Op => A v) hqzero)).1
  have hVQ : V*Q= -Q := by
    ext v : 1
    exact (hker (Q v) (congrArg (fun A : Op => A v) hqzero)).2
  have hQVs : Q*star V= -Q := by
    have hh := congrArg (fun A : Op => star A) hVQ
    rw [star_mul,star_neg Q,hQ.1] at hh
    exact hh
  have hQV : Q*V= -Q := by
    have hh := congrArg (fun A : Op => A*V) hQVs
    rw [mul_assoc,hV.1,mul_one,ProjectionGraph.op_neg_mul] at hh
    have hn := congrArg (fun A : Op => -A) hh
    simpa only [neg_neg] using hn.symm
  have hVsQ : star V*Q= -Q := by
    have hh := congrArg (fun A : Op => star A) hQV
    rw [star_mul,star_neg Q,hQ.1] at hh
    exact hh
  let W : Op := V+(2:ℂ) • Q
  have hW : Unitary W := by
    have hs : star W=star V+(2:ℂ) • Q := by
      change star (V+(2:ℂ) • Q)=_
      rw [star_add V ((2:ℂ) • Q),star_smul (2:ℂ) Q,hQ.1]
      norm_num
    constructor
    · rw [hs]
      change (star V+(2:ℂ) • Q)*(V+(2:ℂ) • Q)=1
      rw [add_mul,mul_add,mul_add,hV.1,mul_smul_comm,smul_mul_assoc,
        smul_mul_smul_comm,hVsQ,hQV,hQ.2]
      module
    · rw [hs]
      change (V+(2:ℂ) • Q)*(star V+(2:ℂ) • Q)=1
      rw [add_mul,mul_add,mul_add,hV.2,mul_smul_comm,smul_mul_assoc,
        smul_mul_smul_comm,hVQ,hQVs,hQ.2]
      module
  have hcQ : Commute h.op Q := by
    change h.op*(1-e)=(1-e)*h.op
    rw [mul_sub,sub_mul,mul_one,one_mul,hre,he.2.1]
  have hcW : Centralizes h.op W :=
    (show Commute h.op V from hcV).add_right (hcQ.smul_right (2:ℂ))
  refine ⟨U,W,hU,hW,hcU,hcW,?_,?_,?_⟩
  · change T+Q=(1/2:ℂ) • (U+(V+(2:ℂ) • Q))
    rw [hm]
    module
  · change (U-1)*Q=0
    rw [sub_mul,one_mul,hUQ,sub_self]
  · change (V+(2:ℂ) • Q-1)*Q=0
    rw [sub_mul,add_mul,one_mul,hVQ,smul_mul_assoc,hQ.2]
    module

#print axioms supported_identity_mean

#print axioms mean_with_kernel
#print axioms supported_kernel_zero
#print axioms supported_mean
end Sigma2.CompilerHonestEncoding
