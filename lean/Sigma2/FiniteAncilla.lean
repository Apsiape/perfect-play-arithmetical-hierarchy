import Sigma2.Purification

/-! Finite ancillary registers in the project's fixed l2 coordinate model.
The original countable ensemble is retained; no environment purification is used. -/
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.FiniteSum
open Coefficients

variable {ι κ ν : Type} [Fintype ι] [DecidableEq ι]

def fiber (e : ι × κ ≃ ν) (v : Space ν) (a : ι) : Space κ :=
  restrict ⟨fun i => e (a,i), fun _ _ h => (Prod.mk.inj (e.injective h)).2⟩ v

@[simp] theorem fiber_apply (e : ι × κ ≃ ν) (v : Space ν) (a : ι) (i : κ) :
    fiber e v a i=v (e (a,i)) := rfl

theorem family_summable (u : ι → Space κ) :
    Summable (fun p : ι × κ => ‖u p.1 p.2‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  exact ⟨fun a => (norm_sq_hasSum (u a)).summable, (hasSum_fintype _).summable⟩

def pack (e : ι × κ ≃ ν) (u : ι → Space κ) : Space ν :=
  ⟨fun i => u (e.symm i).1 (e.symm i).2, memℓp_gen (by
    simpa [Function.comp_def] using
      (family_summable u).comp_injective e.symm.injective)⟩

@[simp] theorem pack_apply (e : ι × κ ≃ ν) (u : ι → Space κ) (a : ι) (i : κ) :
    pack e u (e (a,i))=u a i := by
  change u (e.symm (e (a,i))).1 (e.symm (e (a,i))).2=_
  simp only [Equiv.symm_apply_apply]

@[simp] theorem fiber_pack (e : ι × κ ≃ ν) (u : ι → Space κ) (a : ι) :
    fiber e (pack e u) a=u a := by ext i; exact pack_apply e u a i

@[simp] theorem pack_fiber (e : ι × κ ≃ ν) (v : Space ν) :
    pack e (fiber e v)=v := by
  ext i
  obtain ⟨⟨a,j⟩,rfl⟩ := e.surjective i
  exact pack_apply e (fiber e v) a j

theorem ext_fiber (e : ι × κ ≃ ν) {v w : Space ν}
    (h : ∀ a,fiber e v a=fiber e w a) : v=w := by
  rw [← pack_fiber e v,← pack_fiber e w]
  exact congrArg (pack e) (funext h)

@[simp] theorem fiber_zero (e : ι × κ ≃ ν) (a : ι) : fiber e 0 a=0 := by ext i; rfl
@[simp] theorem fiber_add (e : ι × κ ≃ ν) (v w : Space ν) (a : ι) :
    fiber e (v+w) a=fiber e v a+fiber e w a := by ext i; rfl
@[simp] theorem fiber_smul (e : ι × κ ≃ ν) (c : ℂ) (v : Space ν) (a : ι) :
    fiber e (c • v) a=c • fiber e v a := by ext i; rfl

@[simp] theorem pack_zero (e : ι × κ ≃ ν) : pack e (fun _ => 0)=0 := by
  apply ext_fiber e; intro a; simp
@[simp] theorem pack_add (e : ι × κ ≃ ν) (u v : ι → Space κ) :
    pack e (fun a => u a+v a)=pack e u+pack e v := by
  apply ext_fiber e; intro a; simp
@[simp] theorem pack_smul (e : ι × κ ≃ ν) (c : ℂ) (u : ι → Space κ) :
    pack e (fun a => c • u a)=c • pack e u := by
  apply ext_fiber e; intro a; simp

theorem inner_fibers (e : ι × κ ≃ ν) (v w : Space ν) :
    inner ℂ v w=∑ a,inner ℂ (fiber e v a) (fiber e w a) := by
  rw [lp.inner_eq_tsum,← e.tsum_eq]
  have hs := (lp.summable_inner (𝕜 := ℂ) v w).comp_injective e.injective
  change Summable (fun p : ι × κ => inner ℂ (v (e p)) (w (e p))) at hs
  rw [hs.tsum_prod,tsum_fintype]
  rfl

theorem norm_sq_fibers (e : ι × κ ≃ ν) (v : Space ν) :
    ‖v‖^2=∑ a,‖fiber e v a‖^2 := by
  simp_rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change Complex.reCLM (inner ℂ v v)=∑ a,Complex.reCLM (inner ℂ (fiber e v a) (fiber e v a))
  rw [inner_fibers e,map_sum]

theorem norm_sq_pack (e : ι × κ ≃ ν) (u : ι → Space κ) :
    ‖pack e u‖^2=∑ a,‖u a‖^2 := by rw [norm_sq_fibers e]; simp

def insert (e : ι × κ ≃ ν) (a : ι) : Space κ →ₗᵢ[ℂ] Space ν where
  toFun v := pack e (fun b => if b=a then v else 0)
  map_add' v w := by
    apply ext_fiber e; intro b
    by_cases hb : b=a <;> simp [hb]
  map_smul' c v := by
    apply ext_fiber e; intro b
    by_cases hb : b=a <;> simp [hb]
  norm_map' v := by
    change ‖pack e (fun b => if b=a then v else 0)‖=‖v‖
    have hh : ‖pack e (fun b => if b=a then v else 0)‖^2=‖v‖^2 := by
      rw [norm_sq_pack]; simp [apply_ite]
    nlinarith [norm_nonneg (pack e (fun b => if b=a then v else 0)),norm_nonneg v]

@[simp] theorem fiber_insert (e : ι × κ ≃ ν) (a b : ι) (v : Space κ) :
    fiber e (FiniteSum.insert e a v) b=if b=a then v else 0 := by
  change fiber e (pack e (fun c => if c=a then v else 0)) b=_
  exact fiber_pack e (fun c => if c=a then v else 0) b

theorem fiber_bound (e : ι × κ ≃ ν) (a : ι) (v : Space ν) :
    ‖fiber e v a‖ ≤ ‖v‖ := by
  have hh : ‖fiber e v a‖^2 ≤ ‖v‖^2 := by
    rw [norm_sq_fibers e]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (‖fiber e v i‖)) (Finset.mem_univ a)
  nlinarith [norm_nonneg (fiber e v a),norm_nonneg v]

def project (e : ι × κ ≃ ν) (a : ι) : Space ν →L[ℂ] Space κ :=
  LinearMap.mkContinuous
    { toFun := fun v => fiber e v a
      map_add' := fun v w => fiber_add e v w a
      map_smul' := fun c v => fiber_smul e c v a }
    1 (fun v => by change ‖fiber e v a‖ ≤ 1*‖v‖; simpa only [one_mul] using fiber_bound e a v)

@[simp] theorem project_apply (e : ι × κ ≃ ν) (a : ι) (v : Space ν) :
    project e a v=fiber e v a := rfl

@[simp] theorem insert_adjoint (e : ι × κ ≃ ν) (a : ι) :
    (FiniteSum.insert e a).toContinuousLinearMap.adjoint=project e a := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [inner_fibers e]
  simp only [LinearIsometry.coe_toContinuousLinearMap,fiber_insert]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba; simp [hba]
  · simp

end Sigma2.FiniteSum

namespace Sigma2.FiniteAncilla
open Coefficients FiniteSum TensorLifts

variable (d : ℕ) [NeZero d]

/-- Every local coordinate consists of an old coordinate and a finite register. -/
def coordinates : Fin d × ℕ ≃ ℕ :=
  (Equiv.prodComm (Fin d) ℕ).trans (Nat.divModEquiv d).symm

@[simp] theorem coordinates_apply (a : Fin d) (i : ℕ) :
    coordinates d (a,i)=i*d+a.val := rfl

/-- Literal old-operator tensor identity in these finite-register coordinates. -/
def amplify (A : Op) : Op := ∑ a : Fin d,
  ((FiniteSum.insert (coordinates d) a).toContinuousLinearMap.comp A).comp (project (coordinates d) a)

@[simp] theorem fiber_amplify (A : Op) (v : H) (a : Fin d) :
    fiber (coordinates d) (amplify d A v) a=A (fiber (coordinates d) v a) := by
  change (project (coordinates d) a) ((∑ b : Fin d,
    ((FiniteSum.insert (coordinates d) b).toContinuousLinearMap.comp A).comp (project (coordinates d) b)) v)=_
  simp only [ContinuousLinearMap.sum_apply,map_sum,ContinuousLinearMap.comp_apply,project_apply,
    LinearIsometry.coe_toContinuousLinearMap,fiber_insert]
  simp

@[simp] theorem amplify_one : amplify d 1=1 := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro a
  simp

@[simp] theorem amplify_mul (A B : Op) : amplify d (A*B)=amplify d A*amplify d B := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro a
  simp only [mul_apply_eq_comp,fiber_amplify]

@[simp] theorem amplify_add (A B : Op) : amplify d (A+B)=amplify d A+amplify d B := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro a
  simp only [ContinuousLinearMap.add_apply,fiber_add,fiber_amplify]

@[simp] theorem amplify_smul (c : ℂ) (A : Op) : amplify d (c • A)=c • amplify d A := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro a
  simp only [ContinuousLinearMap.smul_apply,fiber_smul,fiber_amplify]

@[simp] theorem amplify_star (A : Op) : amplify d (star A)=star (amplify d A) := by
  ext v : 1
  apply ext_inner_left ℂ
  intro w
  change inner ℂ w (amplify d (star A) v)=inner ℂ w ((amplify d A).adjoint v)
  rw [ContinuousLinearMap.adjoint_inner_right,inner_fibers (coordinates d),
    inner_fibers (coordinates d)]
  simp only [fiber_amplify,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem amplify_sum {η : Type} (t : Finset η) (A : η → Op) :
    amplify d (∑ i ∈ t,A i)=∑ i ∈ t,amplify d (A i) := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro a
  change _=(project (coordinates d) a) ((∑ i ∈ t,amplify d (A i)) v)
  simp only [fiber_amplify,ContinuousLinearMap.sum_apply,map_sum,project_apply]

theorem amplify_positive (A : Op) (hA : Positive A) : Positive (amplify d A) := by
  constructor
  · intro v w
    change inner ℂ (amplify d A v) w=inner ℂ v (amplify d A w)
    rw [inner_fibers (coordinates d),inner_fibers (coordinates d)]
    simp only [fiber_amplify]
    exact Finset.sum_congr rfl (fun a _ => hA.isSymmetric _ _)
  · intro v
    change 0 ≤ (inner ℂ (amplify d A v) v).re
    rw [inner_fibers (coordinates d)]
    simp only [fiber_amplify,Complex.re_sum]
    exact Finset.sum_nonneg (fun a _ => hA.re_inner_nonneg_left _)

/-- Tensoring a POVM with I uses all local coordinates, with no unused summand. -/
def measurements {s} (M : Measurements s) : Measurements s :=
  TensorLifts.measurements s
    (fun x a => amplify d (M.alice x a)) (fun y b => amplify d (M.bob y b))
    (fun x a => amplify_positive d _ (M.alice_pos x a))
    (fun y b => amplify_positive d _ (M.bob_pos y b))
    (fun x => by rw [← amplify_sum,M.alice_sum,amplify_one])
    (fun y => by rw [← amplify_sum,M.bob_sum,amplify_one])

end Sigma2.FiniteAncilla


