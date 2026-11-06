import Sigma2.CompilerHonestPositive
import Sigma2.RowCornerNormalization

/-! All four source label types admit the same honest unitary dictionary
conventions used by `CompilerScaffold.labelCopy`. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Sigma2.CompilerHonestLabels

/-- The frozen four label decoders, at the operator level. -/
def decodeEncoding (e U V : Op) : LabelType → Op
  | .unitary => e*U
  | .projection => e*((1/2:ℂ) • (1+U))
  | .positive => e*((1/4:ℂ) • ((2:ℂ) • (1:Op)+U+star U))
  | .contraction => e*((1/2:ℂ) • (U+V))

/-- A corner unitary completes by the identity on the orthogonal complement. -/
theorem unitary_completion (e T : Op) (he : Projection e)
    (hTe : T*e=T) (heT : e*T=T) (hT : star T*T=e ∧ T*star T=e) :
    Unitary (T+(1-e)) := by
  let Q : Op := 1-e
  have hQ : Projection Q := Compiler.projection_compl e he
  have hse : star T*e=star T := by
    have hh := congrArg (fun A : Op => star A) heT
    simpa only [star_mul,he.1] using hh
  have hes : e*star T=star T := by
    have hh := congrArg (fun A : Op => star A) hTe
    simpa only [star_mul,he.1] using hh
  have hTQ : T*Q=0 := by dsimp [Q]; rw [mul_sub,mul_one,hTe,sub_self]
  have hQT : Q*T=0 := by dsimp [Q]; rw [sub_mul,one_mul,heT,sub_self]
  have hsQ : star T*Q=0 := by dsimp [Q]; rw [mul_sub,mul_one,hse,sub_self]
  have hQs : Q*star T=0 := by dsimp [Q]; rw [sub_mul,one_mul,hes,sub_self]
  change Unitary (T+Q)
  have hs : star (T+Q)=star T+Q := by rw [star_add T Q,hQ.1]
  constructor
  · rw [hs,add_mul,mul_add,mul_add,hT.1,hsQ,hQT,hQ.2]
    dsimp [Q]
    abel
  · rw [hs,add_mul,mul_add,mul_add,hT.2,hTQ,hQs,hQ.2]
    dsimp [Q]
    abel

/-- A supported projection has a selfadjoint reflection encoding, extended by
identity, so the scaffold's additional reflection-square row is exact. -/
theorem projection_encoding (e T : Op) (he : Projection e) (hT : Projection T)
    (hTe : T*e=T) (heT : e*T=T) :
    ∃ U : Op,Unitary U ∧ star U=U ∧ (U-1)*(1-e)=0 ∧
      decodeEncoding e U 1 .projection=T := by
  let A : Op := (2:ℂ) • T-e
  have hs : star A=A := by
    dsimp only [A]
    rw [star_sub ((2:ℂ) • T) e,star_smul (2:ℂ) T,hT.1,he.1]
    norm_num
  have hsq : A*A=e := by
    dsimp [A]
    simp only [sub_mul,mul_sub,smul_mul_smul_comm,smul_mul_assoc,mul_smul_comm,
      hT.2,hTe,heT,he.2]
    module
  have haL : e*A=A := by dsimp [A]; rw [mul_sub,mul_smul_comm,heT,he.2]
  have haR : A*e=A := by dsimp [A]; rw [sub_mul,smul_mul_assoc,hTe,he.2]
  let U : Op := A+(1-e)
  have hu : Unitary U := RowScalar.corner_reflection_completion e A he hs hsq haL haR
  have hsu : star U=U := by
    dsimp only [U]
    rw [star_add A (1-e),star_sub (1:Op) e,star_one,he.1,hs]
  refine ⟨U,hu,hsu,?_,?_⟩
  · have heq : (U-1)*(1-e)=A-A*e := by
      dsimp [U]
      simp only [sub_mul,add_mul,mul_sub,mul_one,one_mul,he.2]
      noncomm_ring
    rw [heq,haR,sub_self]
  · change e*((1/2:ℂ) • (1+(A+(1-e))))=T
    dsimp [A]
    simp only [mul_smul_comm,mul_add,mul_sub,mul_one,he.2,heT]
    module

/-- All four typed labels are encoded without global faithfulness or a
finite-dimensionality hypothesis on the realization support. -/
theorem typed_encoding (h : Density) (e T : Op) (he : Preliminaries.SupportOf h e)
    (hTe : T*e=T) (heT : e*T=T) (hc : Centralizes h.op T)
    (t : LabelType) (ht : TypedAt e T t) :
    ∃ U V : Op, Unitary U ∧ Unitary V ∧
      Centralizes h.op U ∧ Centralizes h.op V ∧
      (U-1)*(1-e)=0 ∧ (V-1)*(1-e)=0 ∧
      decodeEncoding e U V t=T ∧ (t=.projection → U*U=1) := by
  let Q : Op := 1-e
  have heQ : e*Q=0 := by dsimp [Q]; rw [mul_sub,mul_one,he.1.2,sub_self]
  have hTQ : T*Q=0 := by dsimp [Q]; rw [mul_sub,mul_one,hTe,sub_self]
  have hQ : Projection Q := Compiler.projection_compl e he.1
  have h1 : Unitary (1:Op) := by constructor <;> rw [star_one,one_mul]
  have hc1 : Centralizes h.op (1:Op) := by change h.op*1=1*h.op; rw [mul_one,one_mul]
  have hf1 : ((1:Op)-1)*(1-e)=0 := by rw [sub_self,zero_mul]
  have hre : h.op*e=h.op := by
    have hh := congrArg (fun A : Op => star A) he.2.1
    simpa only [star_mul,he.1.1,h.positive.isSelfAdjoint.star_eq] using hh
  have hce : Commute h.op e := hre.trans he.2.1.symm
  have hcQ : Commute h.op Q := (Commute.one_right _).sub_right hce
  cases t with
  | unitary =>
      have hu : Unitary (T+Q) := unitary_completion e T he.1 hTe heT ht
      have hcu : Centralizes h.op (T+Q) := (show Commute h.op T from hc).add_right hcQ
      have hfix : (T+Q-1)*(1-e)=0 := by
        change (T+Q-1)*Q=0
        rw [sub_mul,add_mul,hTQ,hQ.2,one_mul,zero_add,sub_self]
      refine ⟨T+Q,1,hu,h1,hcu,hc1,hfix,hf1,?_,?_⟩
      · change e*(T+Q)=T
        rw [mul_add,heT,heQ,add_zero]
      · intro hh
        cases hh
  | projection =>
      let U : Op := ((2:ℂ) • T-e)+(1-e)
      -- Replay the explicit construction at this literal witness.
      have hUdef : U=((2:ℂ) • T-e)+(1-e) := rfl
      have hs : star U=U := by
        dsimp only [U]
        rw [star_add ((2:ℂ) • T-e) (1-e),star_sub ((2:ℂ) • T) e,
          star_sub (1:Op) e,star_smul (2:ℂ) T,star_one,he.1.1,ht.1]
        norm_num
      have hsq : U*U=1 := by
        dsimp [U]
        simp only [add_mul,mul_add,sub_mul,mul_sub,smul_mul_smul_comm,smul_mul_assoc,
          mul_smul_comm,one_mul,mul_one,he.1.2,ht.2,hTe,heT]
        module
      have hU : Unitary U := ⟨by rw [hs,hsq],by rw [hs,hsq]⟩
      have hfix : (U-1)*(1-e)=0 := by
        dsimp [U]
        simp only [sub_mul,add_mul,mul_sub,smul_mul_assoc,mul_one,one_mul,he.1.2,hTe]
        module
      have hdec : decodeEncoding e U 1 .projection=T := by
        change e*((1/2:ℂ) • (1+U))=T
        dsimp [U]
        simp only [mul_smul_comm,mul_add,mul_sub,mul_one,he.1.2,heT]
        module
      have hcu : Centralizes h.op U := by
        rw [hUdef]
        exact (((show Commute h.op T from hc).smul_right (2:ℂ)).sub_right hce).add_right hcQ
      refine ⟨U,1,hU,h1,hcu,hc1,hfix,hf1,hdec,?_⟩
      intro _
      calc
        U*U=star U*U := by rw [hs]
        _=1 := hU.1
  | positive =>
      obtain ⟨U,hU,hcu,hfix,hdec⟩ := CompilerHonestPositive.supported_positive_encoding
        h e T he ht.1 ht.2 hTe heT hc
      refine ⟨U,1,hU,h1,hcu,hc1,hfix,hf1,hdec.symm,?_⟩
      intro hh
      cases hh
  | contraction =>
      obtain ⟨U,V,hU,hV,hcu,hcv,hm,hfixU,hfixV⟩ :=
        CompilerHonestEncoding.supported_identity_mean h e T he ht hc hTe
      refine ⟨U,V,hU,hV,hcu,hcv,hfixU,hfixV,?_,?_⟩
      · change e*((1/2:ℂ) • (U+V))=T
        rw [← hm,mul_add,heT,heQ,add_zero]
      · intro hh
        cases hh

#print axioms unitary_completion
#print axioms projection_encoding
#print axioms typed_encoding
end Sigma2.CompilerHonestLabels
