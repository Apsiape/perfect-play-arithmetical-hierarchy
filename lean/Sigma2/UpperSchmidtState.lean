import Sigma2.UpperSchmidtMap

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.UpperSchmidtState
open UpperSchmidtSpectrum UpperSchmidtOperators UpperSchmidtMap

theorem sqrt_summable (q : ℕ → ℝ) (hq : ∀ i,0≤q i) (hs : Summable q) :
    Summable (fun i => Real.sqrt (q i)^2) := by simpa only [Real.sq_sqrt (hq _)] using hs

def vector (q : ℕ → ℝ) (hq : ∀ i,0≤q i) (hs : Summable q) : AB :=
  UpperDiagonalVectors.vector (fun i => Real.sqrt (q i)) (sqrt_summable q hq hs)

@[simp] theorem vector_apply (q : ℕ → ℝ) (hq : ∀ i,0≤q i) (hs : Summable q) (i j : ℕ) :
    vector q hq hs (i,j)=if i=j then (Real.sqrt (q i):ℂ) else 0 := UpperDiagonalVectors.vector_apply _ _ i j

theorem vector_unit (q : ℕ → ℝ) (hq : ∀ i,0≤q i) (hs : Summable q) (ht : (∑' i,q i)=1) :
    ‖vector q hq hs‖=1 := by
  have hh := UpperDiagonalVectors.vector_norm_sq (fun i => Real.sqrt (q i)) (sqrt_summable q hq hs)
  simp only [Real.sq_sqrt (hq _),ht] at hh
  change ‖vector q hq hs‖^2=1 at hh
  nlinarith [norm_nonneg (vector q hq hs)]

theorem right_vector (q : ℕ → ℝ) (hq : ∀ i,0≤q i) (hs : Summable q) (V : Op) (i j : ℕ) :
    TensorLifts.right V (vector q hq hs) (i,j)=(Real.sqrt (q i):ℂ)*entry V j i := by
  rw [TensorLifts.right_coordinates]
  simp only [vector_apply,mul_ite,mul_zero,tsum_ite_eq']
  ring

/-- The completed tensor lifts of the Schmidt maps recover the original vector. -/
theorem map_vector (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hq : ∀ i,0≤q i) (hs : Summable q) (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) :
    (TensorLifts.left (synthesis u hu).toContinuousLinearMap*
      TensorLifts.right (bobMap v hv q u hu he)) (vector q hq hs)=v := by
  ext ij
  rcases ij with ⟨a,b⟩
  change TensorLifts.left (synthesis u hu).toContinuousLinearMap
    (TensorLifts.right (bobMap v hv q u hu he) (vector q hq hs)) (a,b)=v (a,b)
  rw [TensorLifts.left_coordinates,schmidt_coordinates v hv q u hq hu he a b]
  apply tsum_congr
  intro i
  rw [right_vector]
  change (synthesis u hu (basis i)) a*((Real.sqrt (q i):ℂ)*(bobMap v hv q u hu he (basis i)) b)=_
  rw [synthesis_basis,bobMap_basis]
  ring

/-- The normalized diagonal state has no component in the Bob contraction defect. -/
theorem bob_defect_vector (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hq : ∀ i,0≤q i) (hs : Summable q) (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) :
    TensorLifts.right (1-star (bobMap v hv q u hu he)*bobMap v hv q u hu he) (vector q hq hs)=0 := by
  ext ij
  rcases ij with ⟨i,j⟩
  rw [right_vector]
  have hh : entry (1-star (bobMap v hv q u hu he)*bobMap v hv q u hu he) j i=
      (if j=i then 1 else 0)-(if j=i ∧ 0<q j then 1 else 0) := by
    change entry (1 : Op) j i-entry (star (bobMap v hv q u hu he)*bobMap v hv q u hu he) j i=_
    rw [bobMap_gram]
    simp [entry,basis,lp.single_apply,Pi.single_apply,eq_comm]
  rw [hh]
  by_cases hij : j=i
  · subst j
    by_cases hi : 0<q i
    · simp [hi]
    · simp [hi,Real.sqrt_eq_zero_of_nonpos (not_lt.mp hi)]
  · simp [hij]

theorem alice_norm (u : ℕ → H) (hu : Orthonormal ℂ u) : ‖(synthesis u hu).toContinuousLinearMap‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => by simp)

theorem alice_defect (u : ℕ → H) (hu : Orthonormal ℂ u) :
    1-star (synthesis u hu).toContinuousLinearMap*(synthesis u hu).toContinuousLinearMap=0 := by
  have hh := (synthesis u hu).adjoint_comp_self
  change 1-(synthesis u hu).toContinuousLinearMap.adjoint.comp (synthesis u hu).toContinuousLinearMap=0
  rw [hh,sub_self]

/-- Exact Schmidt-coordinate strategy with every original event probability preserved. -/
theorem exists_strategy {s} (S : PureStrategy s) (q : ℕ → ℝ) (u : ℕ → H)
    (hq : ∀ i,0≤q i) (hs : Summable q) (ht : (∑' i,q i)=1) (hu : Orthonormal ℂ u)
    (he : ∀ w,(density S.vector S.unit).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) :
    ∃ T : PureStrategy s,T.vector=vector q hq hs ∧
      ∀ x y a b,T.probability x y a b=S.probability x y a b := by
  let U : Op := (synthesis u hu).toContinuousLinearMap
  let V : Op := bobMap S.vector S.unit q u hu he
  have hU : ‖U‖≤1 := alice_norm u hu
  have hV : ‖V‖≤1 := bobMap_norm S.vector S.unit q u hu he
  let M := UpperPOVMTransport.measurements S.measurements U V hU hV
  let T : PureStrategy s := ⟨M,vector q hq hs,vector_unit q hq hs ht⟩
  refine ⟨T,rfl,?_⟩
  intro x y a b
  have hDU : TensorLifts.left (1-star U*U) (vector q hq hs)=0 := by
    rw [alice_defect,UpperPOVMTransport.left_zero]
    rfl
  have hDV := bob_defect_vector S.vector S.unit q u hq hs hu he
  have hh := UpperPOVMTransport.event_inner S.measurements U V hU hV (vector q hq hs) hDU hDV x y a b
  have hz : (TensorLifts.left U*TensorLifts.right V) (vector q hq hs)=S.vector :=
    map_vector S.vector S.unit q u hq hs hu he
  rw [hz] at hh
  exact congrArg Complex.re hh
end Sigma2.UpperSchmidtState


