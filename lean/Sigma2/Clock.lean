import Sigma2.Tree
import Sigma2.FinitePhaseSector
import Sigma2.PrimePhase
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
open scoped BigOperators
namespace Sigma2.Clock

def PrimitivePhase (ζ : ℂ) (q : ℕ) : Prop := 0<q ∧ ∀ t : ℕ, ζ^t=1 ↔ q ∣ t

/-- Eq. (41), determinant core. This is proved locally, not an external Weyl theorem. -/
theorem finite_weyl_determinant {d : ℕ}
    (J K : Matrix (Fin d) (Fin d) ℂ) (ζ : ℂ)
    (h : J*K=ζ • (K*J)) (hn : (K*J).det≠0) : ζ^d=1 := by
  have heq := congrArg Matrix.det h
  rw [Matrix.det_mul,Matrix.det_smul,Matrix.det_mul] at heq
  have hz : ζ^d*(K.det*J.det)=1*(K.det*J.det) := by
    calc
      _ = J.det*K.det := by simpa using heq.symm
      _ = 1*(K.det*J.det) := by ring
  exact mul_right_cancel₀ (by simpa [Matrix.det_mul] using hn) hz

/-- Section 6.2, the injective counter prevents missing return pulses.
No positive lower bound on C or bounded inverse of the density is used. -/
theorem reader_kernel (W C P T : Op) (hC : Function.Injective C)
    (hfirst : (W-1)*P=0) (hsecond : T*(W-1)=(1/2:ℂ) • (C*(1-P))) :
    ∀ v, (W-1) v=0 ↔ P v=v := by
  intro v
  constructor
  · intro hv
    have hcv : (1/2:ℂ) • (C ((1-P) v))=0 := by
      calc
        _ = (T*(W-1)) v := by rw [hsecond]; rfl
        _ = 0 := by simp [mul_apply_eq_comp,hv]
    have hz : C ((1-P) v)=0 := (smul_eq_zero.mp hcv).resolve_left (by norm_num)
    have he : (1-P) v=0 := hC (by simpa using hz)
    have he' : v-P v=0 := by simpa using he
    exact (sub_eq_zero.mp he').symm
  · intro hp
    have h := congrArg (fun L : Op => L v) hfirst
    simpa [mul_apply_eq_comp,hp] using h

structure Data {P} (R : NormalRealization P) where
  j : Op
  k : Op
  z : Op
  w : Op
  counter : Op
  pulse : Op
  inverse : Op
  unitary : ∀ T ∈ [j,k,z,w], TypedAt R.support T .unitary
  positive_counter : TypedAt R.support counter .positive
  pulse_projection : Projection pulse
  inverse_contraction : Contraction inverse
  supported : ∀ T ∈ [j,k,z,w,counter,pulse,inverse], R.support*T=T ∧ T*R.support=T
  centralizer : ∀ T ∈ [j,k,z,w,counter,pulse,inverse], Centralizes R.density.op T
  weyl : j*k=z*k*j
  central_phase : ∀ T ∈ [j,k,w,counter,pulse,inverse], z*T=T*z
  creation_commute : ∀ a, j*R.creation a=R.creation a*j ∧
    k*R.creation a=R.creation a*k ∧ z*R.creation a=R.creation a*z
  w_root : w*R.label P.root=R.label P.root
  counter_root : counter*R.label P.root=R.label P.root
  w_rec : ∀ a, w*R.creation a=R.creation a*z^(a.val%2)*w^2
  counter_rec : ∀ a, counter*R.creation a=
    ((1/2:ℂ)^(a.val%2)) • (R.creation a*counter^2)
  reader_first : (w-R.support)*pulse=0
  reader_second : inverse*(w-R.support)=(1/2:ℂ) • (counter*(R.support-pulse))

/-- Section 6.1: a finite positive density eigenspace yields a nonzero phase sector. -/
theorem finite_phase_sector {P} (hP : P.admissible) (R : NormalRealization P) (D : Data R) :
    ∃ (q : ℕ) (ζ : ℂ) (ξ : H), PrimitivePhase ζ q ∧ ξ≠0 ∧
      R.label P.root ξ=ξ ∧ D.z ξ=ζ • ξ := by
  classical
  let W : FinitePhaseSector.Triple R :=
    { j := D.j
      k := D.k
      z := D.z
      unitary := by
        intro T hT
        apply D.unitary T
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hT ⊢
        tauto
      supported := by
        intro T hT
        apply D.supported T
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hT ⊢
        tauto
      centralizer := by
        intro T hT
        apply D.centralizer T
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hT ⊢
        tauto
      weyl := D.weyl
      central_phase := by
        intro T hT
        apply D.central_phase T
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hT ⊢
        tauto
      creation_commute := D.creation_commute }
  obtain ⟨d,ζ,ξ,J,K,hd,hξ,hroot,heig,hrel,hdet⟩ := FinitePhaseSector.sector hP R W
  have hpower := finite_weyl_determinant J K ζ hrel hdet
  refine ⟨orderOf ζ,ζ,ξ,⟨?_,?_⟩,hξ,hroot,heig⟩
  · exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨d,hd,hpower⟩)
  · intro t
    exact orderOf_dvd_iff_pow_eq_one.symm

/-- Eq. (44), clock and counter on every word descendant. -/
theorem coordinate_clock {P} (hP : P.admissible) (R : NormalRealization P) (D : Data R)
    (ξ : H) (hξ : R.label P.root ξ=ξ) (w : Tree.Word) :
    D.w (Tree.wordOp R w ξ)=Tree.wordOp R w ((D.z^(Tree.yCoord w)) ξ) ∧
    D.counter (Tree.wordOp R w ξ)=((1/2:ℂ)^(Tree.yCoord w)) • Tree.wordOp R w ξ := by
  have hs := D.supported D.z (by simp)
  have hzword (w : Tree.Word) : Commute D.z (Tree.wordOp R w) := by
    induction w with
    | nil => exact hs.2.trans hs.1.symm
    | cons a w ih =>
      exact Commute.mul_right (D.creation_commute a).2.2 ih
  have hzw : Commute D.z D.w := D.central_phase D.w (by simp)
  have hr : R.support ξ=ξ := by
    rw [← hξ]
    exact congrArg (fun A : Op => A ξ) (R.label_supported P.root).1
  have root_action (T : Op) (ht : T*R.label P.root=R.label P.root) : T ξ=ξ := by
    have hh := congrArg (fun A : Op => A ξ) ht
    simpa only [mul_apply_eq_comp,hξ] using hh
  induction w with
  | nil =>
    simpa only [Tree.wordOp,Tree.yCoord,pow_zero,one_apply_eq_self,one_smul,hr] using
      And.intro (root_action D.w D.w_root) (root_action D.counter D.counter_root)
  | cons a w ih =>
    let v := Tree.wordOp R w ξ
    let y := Tree.yCoord w
    have hv : D.w v=(D.z^y) v := by
      change D.w (Tree.wordOp R w ξ)=(D.z^Tree.yCoord w) (Tree.wordOp R w ξ)
      rw [ih.1]
      exact congrArg (fun A : Op => A ξ) ((hzword w).pow_left (Tree.yCoord w)).eq.symm
    have hv2 : (D.w^2) v=(D.z^(2*y)) v := by
      calc
        _ = D.w (D.w v) := rfl
        _ = D.w ((D.z^y) v) := by rw [hv]
        _ = (D.z^y) (D.w v) :=
          congrArg (fun A : Op => A v) (hzw.pow_left y).eq.symm
        _ = (D.z^y) ((D.z^y) v) := by rw [hv]
        _ = _ := by rw [two_mul,pow_add]; rfl
    have hc2 : (D.counter^2) v=((1/2:ℂ)^(2*y)) • v := by
      change D.counter (D.counter v)=_
      have hc : D.counter v=((1/2:ℂ)^y) • v := ih.2
      rw [hc,map_smul,hc,smul_smul,← pow_add,← two_mul]
    constructor
    · change D.w (R.creation a v)=R.creation a (Tree.wordOp R w ((D.z^(2*y+a.val%2)) ξ))
      calc
        _ = R.creation a ((D.z^(a.val%2)) ((D.w^2) v)) :=
          congrArg (fun A : Op => A v) (D.w_rec a)
        _ = R.creation a ((D.z^(a.val%2+2*y)) v) := by rw [hv2,pow_add]; rfl
        _ = R.creation a (Tree.wordOp R w ((D.z^(2*y+a.val%2)) ξ)) := by
          rw [Nat.add_comm (a.val%2)]
          apply congrArg (R.creation a)
          exact congrArg (fun A : Op => A ξ) ((hzword w).pow_left (2*y+a.val%2)).eq
    · change D.counter (R.creation a v)=((1/2:ℂ)^(2*y+a.val%2)) • R.creation a v
      calc
        _ = ((1/2:ℂ)^(a.val%2)) • R.creation a ((D.counter^2) v) :=
          congrArg (fun A : Op => A v) (D.counter_rec a)
        _ = _ := by rw [hc2,map_smul,smul_smul,← pow_add,Nat.add_comm (a.val%2)]

/-- Counter injectivity on the state support, despite spectral accumulation at zero. -/
theorem counter_injective_on_support {P} (hP : P.admissible) (R : NormalRealization P)
    (D : Data R) (v : H) (hv : R.support v=v) (hz : D.counter v=0) : v=0 := by
  have hp := TreeFoundation.root_projection hP R
  have hc : star D.counter=D.counter := D.positive_counter.1.isSelfAdjoint.star_eq
  have hzword (w : Tree.Word) : Tree.wordProjection R w v=0 := by
    let A := Tree.wordOp R w
    have hs : star (Tree.wordProjection R w)=Tree.wordProjection R w := by
      dsimp [Tree.wordProjection]
      rw [star_mul,star_mul,star_star,hp.1]
      noncomm_ring
    have hdiag : D.counter*Tree.wordProjection R w=
        ((1/2:ℂ)^Tree.yCoord w) • Tree.wordProjection R w := by
      apply ContinuousLinearMap.ext
      intro u
      have hroot : R.label P.root (R.label P.root (star A u))=
          R.label P.root (star A u) := congrArg (fun T : Op => T (star A u)) hp.2
      exact (coordinate_clock hP R D _ hroot w).2
    have hdiag' : Tree.wordProjection R w*D.counter=
        ((1/2:ℂ)^Tree.yCoord w) • Tree.wordProjection R w := by
      have hh := congrArg star hdiag
      simpa [star_mul,star_smul,hs,hc] using hh
    have hh := congrArg (fun T : Op => T v) hdiag'
    have he : ((1/2:ℂ)^Tree.yCoord w) • Tree.wordProjection R w v=0 := by
      simpa only [mul_apply_eq_comp,hz,map_zero,ContinuousLinearMap.smul_apply] using hh.symm
    exact (smul_eq_zero.mp he).resolve_left (pow_ne_zero _ (by norm_num))
  have ht := (Tree.fock_decomposition hP R).2.2.2.1 v
  simpa only [hzword,tsum_zero,hv] using ht.symm

/-- Eq. (46), exact scalar divisibility pulse on every chosen finite-order sector. -/
theorem exact_return {P} (hP : P.admissible) (R : NormalRealization P) (D : Data R)
    (q : ℕ) (ζ : ℂ) (hζ : PrimitivePhase ζ q) (ξ : H)
    (hξ : R.label P.root ξ=ξ) (heig : D.z ξ=ζ • ξ) (w : Tree.Word) :
    D.pulse (Tree.wordOp R w ξ)=
      if q ∣ Tree.yCoord w then Tree.wordOp R w ξ else 0 := by
  let v := Tree.wordOp R w ξ
  let y := Tree.yCoord w
  have hsupport (u : Tree.Word) : R.support*Tree.wordOp R u=Tree.wordOp R u := by
    induction u with
    | nil => exact R.support_projection.2
    | cons a u ih =>
      change R.support*(R.creation a*Tree.wordOp R u)=R.creation a*Tree.wordOp R u
      rw [← mul_assoc,(R.creation_supported a).1]
  have hv : R.support v=v := congrArg (fun T : Op => T ξ) (hsupport w)
  have hpow (n : ℕ) : (D.z^n) ξ=ζ^n • ξ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',mul_apply_eq_comp,ih,map_smul,heig,smul_smul,pow_succ]
  have hW : D.w v=ζ^y • v := by
    change D.w (Tree.wordOp R w ξ)=_
    rw [(coordinate_clock hP R D ξ hξ w).1,hpow,map_smul]
  have hps := D.supported D.pulse (by simp)
  have hwp : D.w*D.pulse=D.pulse := by
    have hh := D.reader_first
    rw [sub_mul,hps.1] at hh
    exact sub_eq_zero.mp hh
  have hswp : star D.w*D.pulse=D.pulse := by
    calc
      _ = star D.w*(D.w*D.pulse) := by rw [hwp]
      _ = (star D.w*D.w)*D.pulse := by noncomm_ring
      _ = _ := by rw [(D.unitary D.w (by simp)).1,hps.1]
  have hpw : D.pulse*D.w=D.pulse := by
    have hh := congrArg star hswp
    simpa only [star_mul,star_star,D.pulse_projection.1] using hh
  change D.pulse v=if q ∣ y then v else 0
  by_cases hy : q ∣ y
  · rw [if_pos hy]
    have hWv : (D.w-R.support) v=0 := by
      simp only [sub_apply,hW,(hζ.2 y).mpr hy,one_smul,hv,sub_self]
    have hcv : (1/2:ℂ) • D.counter ((R.support-D.pulse) v)=0 := by
      calc
        _ = (D.inverse*(D.w-R.support)) v := by rw [D.reader_second]; rfl
        _ = 0 := by simp only [mul_apply_eq_comp,hWv,map_zero]
    have hcz : D.counter ((R.support-D.pulse) v)=0 :=
      (smul_eq_zero.mp hcv).resolve_left (by norm_num)
    have hfix : R.support ((R.support-D.pulse) v)=(R.support-D.pulse) v := by
      simp only [sub_apply,map_sub,hv]
      have hh := congrArg (fun T : Op => T v) hps.1
      exact congrArg (fun t : H => v-t) hh
    have hh := counter_injective_on_support hP R D _ hfix hcz
    have he : v-D.pulse v=0 := by simpa only [sub_apply,hv] using hh
    exact (sub_eq_zero.mp he).symm
  · rw [if_neg hy]
    have hn : ζ^y-1≠0 := sub_ne_zero.mpr (fun he => hy ((hζ.2 y).mp he))
    have hh := congrArg (fun T : Op => T v) hpw
    have he : (ζ^y-1) • D.pulse v=0 := by
      have hh' : ζ^y • D.pulse v=D.pulse v := by
        simpa only [mul_apply_eq_comp,hW,map_smul] using hh
      rw [sub_smul,one_smul,hh',sub_self]
    exact (smul_eq_zero.mp he).resolve_left hn

/-- Lemma 6.1, Good primitive phase. -/
theorem lemma_6_1_good_primitive_phase (q : ℕ) (hq : Nat.Prime q) :
    ∃ ζ : ℂ, PrimitivePhase ζ q ∧ ∀ t : ℕ, 0<t → ¬ q ∣ t →
      (1/2:ℝ)^(t+1) ≤ ‖ζ^t-1‖ := by
  obtain ⟨ζ,hζ,hgood⟩ := Sigma2.PrimePhase.good_root q hq
  exact ⟨ζ,⟨hq.pos,fun t => hζ.pow_eq_one_iff_dvd t⟩,hgood⟩

def readerScalar (q : ℕ) (ζ : ℂ) (y : ℕ) : ℂ :=
  if q ∣ y then 0 else (1/2:ℂ)^(y+1)/(ζ^y-1)

/-- Eq. (47), the prescribed inverse is a contraction and solves the reader equation. -/
theorem bounded_reader (q : ℕ) (ζ : ℂ) (hζ : PrimitivePhase ζ q)
    (hg : ∀ t : ℕ,0<t → ¬ q ∣ t → (1/2:ℝ)^(t+1) ≤ ‖ζ^t-1‖) :
    ∀ y,‖readerScalar q ζ y‖ ≤ 1 ∧
      readerScalar q ζ y*(ζ^y-1)=(if q ∣ y then 0 else (1/2:ℂ)^(y+1)) := by
  intro y
  by_cases hy : q ∣ y
  · simp [readerScalar,hy]
  · have hypos : 0<y := Nat.pos_of_ne_zero (by intro h;subst y;exact hy (dvd_zero q))
    have hn : ζ^y-1≠0 := sub_ne_zero.mpr (fun h => hy ((hζ.2 y).mp h))
    constructor
    · rw [readerScalar,if_neg hy,norm_div,norm_pow]
      have hnorm : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
      rw [hnorm]
      exact (div_le_one (norm_pos_iff.mpr hn)).mpr (hg y hypos hy)
    · simp only [readerScalar,if_neg hy]
      exact div_mul_cancel₀ _ hn

end Sigma2.Clock

