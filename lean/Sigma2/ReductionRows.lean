import Sigma2.ReductionPresentation

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace Sigma2.ReductionRows
open Sigma2.Tree Sigma2.Reduction Sigma2.Reduction.Syntax
variable {M : Automaton} (A : NormalRealization (applicationPresentation M))

@[simp] theorem eval_I : I.eval A.support A.label = A.support := by simp [I, Expr.eval]
@[simp] theorem eval_L (i : ℕ) : (L i).eval A.support A.label = A.label i := rfl
theorem eval_supported (p : Expr) :
    A.support*p.eval A.support A.label=p.eval A.support A.label ∧
      p.eval A.support A.label*A.support=p.eval A.support A.label := by
  induction p with
  | scalar q => simp [Expr.eval, mul_smul_comm, smul_mul_assoc, A.support_projection.2]
  | label i => exact A.label_supported i
  | add p q hp hq => simp [Expr.eval, mul_add, add_mul, hp.1, hp.2, hq.1, hq.2]
  | mul p q hp hq =>
    constructor
    · rw [Expr.eval, ← mul_assoc, hp.1]
    · rw [Expr.eval, mul_assoc, hq.2]
  | adj p hp =>
    constructor
    · simpa only [star_mul, A.support_projection.1, Expr.eval] using congrArg star hp.2
    · simpa only [star_mul, A.support_projection.1, Expr.eval] using congrArg star hp.1

@[simp] theorem eval_sub (p q : Expr) :
    (sub p q).eval A.support A.label = p.eval A.support A.label-q.eval A.support A.label := by
  simp [sub, neg, Expr.eval, smul_mul_assoc, (eval_supported A q).1, sub_eq_add_neg]
  module
@[simp] theorem eval_mul3 (p q r : Expr) :
    (mul3 p q r).eval A.support A.label = p.eval A.support A.label*q.eval A.support A.label*r.eval A.support A.label := rfl
@[simp] theorem eval_sym (c : ℕ) : (sym c).eval A.support A.label = A.label (12+c) := rfl

theorem typed_0 : TypedAt A.support (A.label 0) .projection := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨0, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_1 : TypedAt A.support (A.label 1) .unitary := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨1, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_2 : TypedAt A.support (A.label 2) .unitary := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨2, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_3 : TypedAt A.support (A.label 3) .projection := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨3, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_4 : TypedAt A.support (A.label 4) .projection := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨4, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_5 : TypedAt A.support (A.label 5) .unitary := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨5, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_6 : TypedAt A.support (A.label 6) .positive := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨6, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_7 : TypedAt A.support (A.label 7) .unitary := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨7, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_8 : TypedAt A.support (A.label 8) .unitary := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨8, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_9 : TypedAt A.support (A.label 9) .unitary := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨9, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_10 : TypedAt A.support (A.label 10) .projection := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨10, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_11 : TypedAt A.support (A.label 11) .contraction := by
  simpa [applicationPresentation, buildPresentation] using
    A.typed ⟨11, by simp [applicationPresentation, buildPresentation] <;> omega⟩

theorem typed_symbol (c : Symbol M) : Projection (A.label (12+c.val)) := by
  have hc := c.isLt
  have ht := A.typed ⟨12+c.val, by simp [applicationPresentation, buildPresentation] <;> omega⟩
  change TypedAt A.support (A.label (12+c.val))
    (([.projection,.unitary,.unitary,.projection,.projection,.unitary,.positive,
      .unitary,.unitary,.unitary,.projection,.contraction] ++
      List.replicate (M.extraSymbols+3) .projection)[12+c.val]'(by simp; omega)) at ht
  rw [List.getElem_append_right (by simp)] at ht
  simpa [TypedAt] using ht

-- Membership of a fixed central row, isolated from the variable transition list.
theorem fixed_row (p : Expr)
    (h : p ∈ [sub (.mul (L 1) (L 0)) (L 0),sub (.mul (L 2) (L 0)) (L 0),
       sub (.mul (L 3) (L 0)) (L 0),sub (.mul (L 4) (L 0)) (L 0),
       sub (.mul (L 5) (L 0)) (L 0),sub (.mul (L 6) (L 0)) (L 0),
       sub (.mul (L 8) (L 9)) (mul3 (L 7) (L 9) (L 8)),
       .mul (sub (L 5) I) (L 10),
       sub (.mul (L 11) (sub (L 5) I)) (.mul (.scalar (1/2)) (.mul (L 6) (sub I (L 10)))),
       sub (mul3 (sym 0) (L 3) (L 4)) (.mul (L 3) (L 4)),
       sub (mul3 (sym 1) (sub I (L 3)) (L 4)) (.mul (sub I (L 3)) (L 4)),
       sym 2,sub (sum ((List.ofFn (fun c : Symbol M => c)).map (fun c => sym c.val))) I]) :
    p.eval A.support A.label=0 := by
  apply A.central_equations p
  exact List.mem_append_left _ (List.mem_append_left _ h)

theorem root_row (i : ℕ) (hi : i ∈ [1,2,3,4,5,6]) :
    A.label i*A.label 0=A.label 0 := by
  apply sub_eq_zero.mp
  have h := fixed_row A (sub (.mul (L i) (L 0)) (L 0))
  apply (by simpa [Expr.eval] using h) -- membership remains finite
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

-- Endpoint identities and the two zero rows.

theorem x_endpoint (b : Fin 2) (r : Expr × Fin 4 × Fin 4 × Expr)
    (h : r ∈ [(L 1,⟨b.val,by omega⟩,⟨b.val+2,by omega⟩,I),
       (L 1,⟨b.val+2,by omega⟩,⟨b.val,by omega⟩,L 1),
       (L 3,⟨b.val,by omega⟩,⟨b.val,by omega⟩,L 3)]) :
    r.1.eval A.support A.label*A.creation r.2.1 =
      A.creation r.2.2.1*r.2.2.2.eval A.support A.label := by
  apply A.endpoint_equations
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨b,List.mem_ofFn.mpr ⟨b,rfl⟩,h⟩

theorem y_endpoint (a : Fin 2) (r : Expr × Fin 4 × Fin 4 × Expr)
    (h : r ∈ [(L 2,⟨2*a.val,by omega⟩,⟨2*a.val+1,by omega⟩,I),
       (L 2,⟨2*a.val+1,by omega⟩,⟨2*a.val,by omega⟩,L 2),
       (L 4,⟨2*a.val,by omega⟩,⟨2*a.val,by omega⟩,L 4)]) :
    r.1.eval A.support A.label*A.creation r.2.1 =
      A.creation r.2.2.1*r.2.2.2.eval A.support A.label := by
  apply A.endpoint_equations
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨a,List.mem_ofFn.mpr ⟨a,rfl⟩,h⟩

theorem clock_endpoint (a : Fin 4) (r : Expr × Fin 4 × Fin 4 × Expr)
    (h : r ∈ [(L 5,a,a,.mul (if a.val%2=0 then I else L 7) (.mul (L 5) (L 5))),
       (L 6,a,a,.mul (.scalar (if a.val%2=0 then 1 else 1/2)) (.mul (L 6) (L 6))),
       (L 7,a,a,L 7),(L 8,a,a,L 8),(L 9,a,a,L 9)]) :
    r.1.eval A.support A.label*A.creation r.2.1 =
      A.creation r.2.2.1*r.2.2.2.eval A.support A.label := by
  apply A.endpoint_equations
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨a,List.mem_ofFn.mpr ⟨a,rfl⟩,h⟩

def coordinates : Coordinates A where
  ux := A.label 1
  uy := A.label 2
  px := A.label 3
  py := A.label 4
  ux_unitary := typed_1 A
  uy_unitary := typed_2 A
  px_projection := typed_3 A
  py_projection := typed_4 A
  supported := by
    intro T h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> exact A.label_supported _
  centralizer := by
    intro T h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> exact A.centralizer _
  ux_root := root_row A 1 (by simp)
  uy_root := root_row A 2 (by simp)
  px_root := root_row A 3 (by simp)
  py_root := root_row A 4 (by simp)
  ux_rec := by
    intro b
    constructor
    · simpa [Expr.eval, A.creation_supported] using
        x_endpoint A b (L 1,⟨b.val,by omega⟩,⟨b.val+2,by omega⟩,I) (by simp)
    · exact x_endpoint A b (L 1,⟨b.val+2,by omega⟩,⟨b.val,by omega⟩,L 1) (by simp)
  uy_rec := by
    intro a
    constructor
    · simpa [Expr.eval, A.creation_supported] using
        y_endpoint A a (L 2,⟨2*a.val,by omega⟩,⟨2*a.val+1,by omega⟩,I) (by simp)
    · exact y_endpoint A a (L 2,⟨2*a.val+1,by omega⟩,⟨2*a.val,by omega⟩,L 2) (by simp)
  px_rec := by
    intro b
    constructor
    · exact x_endpoint A b (L 3,⟨b.val,by omega⟩,⟨b.val,by omega⟩,L 3) (by simp)
    · apply A.zero_equations (L 3,⟨b.val+2,by omega⟩)
      exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨b,rfl⟩)
  py_rec := by
    intro a
    constructor
    · exact y_endpoint A a (L 4,⟨2*a.val,by omega⟩,⟨2*a.val,by omega⟩,L 4) (by simp)
    · apply A.zero_equations (L 4,⟨2*a.val+1,by omega⟩)
      exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨a,rfl⟩)

theorem phase_commute (i : ℕ)
    (hi : i ∈ [0,1,2,3,4,5,6,8,9,10,11] ++
      (List.ofFn (fun c : Symbol M => c)).map (fun c => 12+c.val)) :
    A.label 7*A.label i=A.label i*A.label 7 := by
  apply sub_eq_zero.mp
  have h := A.central_equations (comm (L 7) (L i))
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨i,hi,rfl⟩)))
  simpa [Syntax.comm,Expr.eval] using h

def clockData : Clock.Data A where
  j := A.label 8
  k := A.label 9
  z := A.label 7
  w := A.label 5
  counter := A.label 6
  pulse := A.label 10
  inverse := A.label 11
  unitary := by
    intro T h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact typed_8 A
    · exact typed_9 A
    · exact typed_7 A
    · exact typed_5 A
  positive_counter := typed_6 A
  pulse_projection := typed_10 A
  inverse_contraction := typed_11 A
  supported := by
    intro T h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact A.label_supported _
  centralizer := by
    intro T h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact A.centralizer _
  weyl := by
    apply sub_eq_zero.mp
    simpa [Expr.eval] using fixed_row A
      (sub (.mul (L 8) (L 9)) (mul3 (L 7) (L 9) (L 8))) (by simp)
  central_phase := by
    intro T h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> apply phase_commute <;> simp
  creation_commute := by
    intro a
    exact ⟨clock_endpoint A a (L 8,a,a,L 8) (by simp),
      clock_endpoint A a (L 9,a,a,L 9) (by simp),
      clock_endpoint A a (L 7,a,a,L 7) (by simp)⟩
  w_root := root_row A 5 (by simp)
  counter_root := root_row A 6 (by simp)
  w_rec := by
    intro a
    have h := clock_endpoint A a
      (L 5,a,a,.mul (if a.val%2=0 then I else L 7) (.mul (L 5) (L 5))) (by simp)
    fin_cases a <;> simpa [Expr.eval, pow_two, ← mul_assoc, A.creation_supported] using h
  counter_rec := by
    intro a
    have h := clock_endpoint A a
      (L 6,a,a,.mul (.scalar (if a.val%2=0 then 1 else 1/2)) (.mul (L 6) (L 6))) (by simp)
    fin_cases a <;> norm_num [Expr.eval, pow_two, ← mul_assoc, A.creation_supported,
      mul_smul_comm, smul_mul_assoc] at h ⊢ <;> exact h
  reader_first := by
    simpa [Expr.eval] using fixed_row A (.mul (sub (L 5) I) (L 10)) (by simp)
  reader_second := by
    apply sub_eq_zero.mp
    simpa [Expr.eval, smul_mul_assoc, ← mul_assoc, A.label_supported] using fixed_row A
      (sub (.mul (L 11) (sub (L 5) I))
        (.mul (.scalar (1/2)) (.mul (L 6) (sub I (L 10))))) (by simp)

#print axioms coordinates
#print axioms clockData
end Sigma2.ReductionRows
