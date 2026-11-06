import Sigma2.FiniteAncilla

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.FiniteAncilla
open Coefficients FiniteSum TensorLifts
variable (d : ℕ) [NeZero d]

/-- Both finite ancillary indices precede the original bipartite coordinates. -/
def bipCoordinates : ((Fin d × Fin d) × (ℕ × ℕ)) ≃ (ℕ × ℕ) :=
  (Equiv.prodProdProdComm (Fin d) (Fin d) ℕ ℕ).trans
    ((coordinates d).prodCongr (coordinates d))

@[simp] theorem bipCoordinates_apply (a b : Fin d) (i j : ℕ) :
    bipCoordinates d ((a,b),(i,j))=(coordinates d (a,i),coordinates d (b,j)) := rfl

def amplitude : ℂ := (Real.sqrt (1/(d:ℝ)):ℂ)

theorem amplitude_square : amplitude d*amplitude d=(1/(d:ℝ):ℝ) := by
  unfold amplitude
  exact_mod_cast Real.mul_self_sqrt (show 0≤1/(d:ℝ) by positivity)

@[simp] theorem amplitude_star : star (amplitude d)=amplitude d := Complex.conj_ofReal _

/-- v tensored with the finite maximally entangled unit vector. -/
def entangleVector (v : AB) : AB := pack (bipCoordinates d)
  (fun ab => if ab.1=ab.2 then amplitude d • v else 0)

@[simp] theorem fiber_entangleVector (v : AB) (a b : Fin d) :
    fiber (bipCoordinates d) (entangleVector d v) (a,b)=
      if a=b then amplitude d • v else 0 := by
  exact fiber_pack (bipCoordinates d) _ (a,b)

theorem entangleVector_inner (v w : AB) :
    inner ℂ (entangleVector d v) (entangleVector d w)=inner ℂ v w := by
  rw [inner_fibers (bipCoordinates d),Fintype.sum_prod_type]
  have he (a b : Fin d) :
      inner ℂ (fiber (bipCoordinates d) (entangleVector d v) (a,b))
        (fiber (bipCoordinates d) (entangleVector d w) (a,b))=
      if a=b then (1/(d:ℝ):ℂ)*inner ℂ v w else 0 := by
    by_cases hab : a=b
    · simp only [fiber_entangleVector,hab,ite_true,inner_smul_left,inner_smul_right]
      change amplitude d*(star (amplitude d)*inner ℂ v w)=_
      rw [amplitude_star,← mul_assoc,amplitude_square]
      push_cast
      rfl
    · simp [fiber_entangleVector,hab]
  simp_rw [he]
  have hn : (d:ℂ)≠0 := by exact_mod_cast NeZero.ne d
  simp [← Finset.mul_sum,hn]

def entangle : AB →ₗᵢ[ℂ] AB := LinearMap.isometryOfInner
  { toFun := entangleVector d
    map_add' := by
      intro v w
      apply ext_fiber (bipCoordinates d)
      intro ⟨a,b⟩
      by_cases hab : a=b <;> simp [fiber_entangleVector,hab,smul_add]
    map_smul' := by
      intro c v
      apply ext_fiber (bipCoordinates d)
      intro ⟨a,b⟩
      by_cases hab : a=b <;> simp [fiber_entangleVector,hab,smul_smul,mul_comm] }
  (entangleVector_inner d)

@[simp] theorem fiber_entangle (v : AB) (a b : Fin d) :
    fiber (bipCoordinates d) (entangle d v) (a,b)=
      if a=b then amplitude d • v else 0 := fiber_entangleVector d v a b

@[simp] theorem entangle_apply (v : AB) (a b : Fin d) (i j : ℕ) :
    entangle d v (coordinates d (a,i),coordinates d (b,j))=
      if a=b then amplitude d*v (i,j) else 0 := by
  change (fiber (bipCoordinates d) (entangle d v) (a,b)) (i,j)=_
  rw [fiber_entangle]
  split_ifs <;> rfl

@[simp] theorem amplify_apply (A : Op) (v : H) (a : Fin d) (i : ℕ) :
    amplify d A v (coordinates d (a,i))=A (fiber (coordinates d) v a) i :=
  congrArg (fun u : H => u i) (fiber_amplify d A v a)

@[simp] theorem fiber_left (A : Op) (v : AB) (a b : Fin d) :
    fiber (bipCoordinates d) (left (amplify d A) v) (a,b)=
      left A (fiber (bipCoordinates d) v (a,b)) := by
  ext ⟨i,j⟩
  change left (amplify d A) v (coordinates d (a,i),coordinates d (b,j))=_
  rw [left_apply,amplify_apply,left_apply]
  rfl

@[simp] theorem fiber_right (B : Op) (v : AB) (a b : Fin d) :
    fiber (bipCoordinates d) (right (amplify d B) v) (a,b)=
      right B (fiber (bipCoordinates d) v (a,b)) := by
  ext ⟨i,j⟩
  change right (amplify d B) v (coordinates d (a,i),coordinates d (b,j))=_
  rw [right_apply,amplify_apply,right_apply]
  rfl

theorem left_entangle (A : Op) (v : AB) :
    left (amplify d A) (entangle d v)=entangle d (left A v) := by
  apply ext_fiber (bipCoordinates d)
  intro ⟨a,b⟩
  rw [fiber_left,fiber_entangle,fiber_entangle]
  split_ifs <;> simp only [map_smul,map_zero]

theorem right_entangle (B : Op) (v : AB) :
    right (amplify d B) (entangle d v)=entangle d (right B v) := by
  apply ext_fiber (bipCoordinates d)
  intro ⟨a,b⟩
  rw [fiber_right,fiber_entangle,fiber_entangle]
  split_ifs <;> simp only [map_smul,map_zero]

/-- All original ensemble weights and all old measurements are retained. -/
def strategy {s} (S : NormalStrategy s) : NormalStrategy s where
  measurements := measurements d S.measurements
  vector k := entangle d (S.vector k)
  unit k := by rw [(entangle d).norm_map,S.unit k]
  weight := S.weight
  weight_nonneg := S.weight_nonneg
  weight_summable := S.weight_summable
  weight_sum := S.weight_sum

/-- Componentwise exact preservation, before taking any ensemble sum. -/
theorem component_probability {s} (S : NormalStrategy s) (k : ℕ) (x y a b) :
    ((strategy d S).component k).probability x y a b=(S.component k).probability x y a b := by
  change (inner ℂ (entangle d (S.vector k))
    (left (amplify d (S.measurements.alice x a))
      (right (amplify d (S.measurements.bob y b)) (entangle d (S.vector k))))).re=_
  rw [right_entangle,left_entangle,(entangle d).inner_map_map]
  rw [PureStrategy.probability,NormalStrategy.component,measurements_left,measurements_right]
  rfl

/-- Arbitrary mixed old correlations are unchanged, without selecting a component. -/
theorem probability {s} (S : NormalStrategy s) (x y a b) :
    (strategy d S).probability x y a b=S.probability x y a b := by
  unfold NormalStrategy.probability
  apply tsum_congr
  intro k
  rw [component_probability]
  rfl

theorem perfect (G : Game) (S : NormalStrategy G.scenario) (hS : Perfect G S) :
    Perfect G (strategy d S) := by
  simpa only [Perfect,loss,probability] using hS

end Sigma2.FiniteAncilla
