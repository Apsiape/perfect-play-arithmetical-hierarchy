import Sigma2.UpperRealArithmetic

/-! Bounded existential sentences are uniformly Π⁰₁, without a decision procedure.

For a conjunctive sentence of closed atoms (`p = 0` and `0 ≤ p`) and a natural bound
`B`, truth by a valuation with every coordinate in `[-B,B]` holds exactly when no
resolution `k` yields a rational grid certificate of emptiness. The certificate checks,
at every point of the grid of spacing `1/(k+1)` on the box, that some atom is violated
by more than its Lipschitz bound times `1/(k+1)`. Soundness is the Lipschitz estimate;
completeness is compactness of the box (Cantor's intersection theorem). The test is an
exact finite rational computation, hence computable. -/
set_option maxHeartbeats 400000
namespace Sigma2.UpperGridCertificate
open Sigma2.UpperRealArithmetic Sigma2.UpperCoding
open scoped BigOperators

/-! ### Computable list folds -/

theorem foldl_take {β σ : Type*} (l : List β) (f : σ → β → σ) (g : σ) (n : ℕ) :
    Nat.rec (motive := fun _ => σ) g (fun k acc => (l[k]?).elim acc (f acc)) n =
      (l.take n).foldl f g := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Nat.rec (motive := fun _ => σ) g (fun k acc => (l[k]?).elim acc (f acc)) (n+1) =
        (l[n]?).elim (Nat.rec (motive := fun _ => σ) g (fun k acc => (l[k]?).elim acc (f acc)) n)
          (f (Nat.rec (motive := fun _ => σ) g (fun k acc => (l[k]?).elim acc (f acc)) n)) := rfl
    rw [h, ih, List.take_add_one, List.foldl_append]
    cases l[n]? <;> rfl

theorem foldl_computable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {l : α → List β} {g : α → σ} {f : α → σ → β → σ}
    (hl : Computable l) (hg : Computable g)
    (hf : Computable (fun p : α × σ × β => f p.1 p.2.1 p.2.2)) :
    Computable (fun a => (l a).foldl (f a) (g a)) := by
  have ho : Computable (fun p : α × ℕ × σ => (l p.1)[p.2.1]?) :=
    Computable.list_getElem?.comp (hl.comp Computable.fst) (Computable.fst.comp Computable.snd)
  have hs : Computable (fun p : α × ℕ × σ => ((l p.1)[p.2.1]?).elim p.2.2 (f p.1 p.2.2)) := by
    refine (Computable.option_casesOn ho (Computable.snd.comp Computable.snd)
      (hf.comp ((Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
          Computable.snd))).to₂).of_eq ?_
    intro p
    cases (l p.1)[p.2.1]? <;> rfl
  refine (Computable.nat_rec (Computable.list_length.comp hl) hg hs.to₂).of_eq ?_
  intro a
  exact (foldl_take (l a) (f a) (g a) _).trans (by rw [List.take_length])

theorem foldr_computable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {l : α → List β} {g : α → σ} {f : α → β → σ → σ}
    (hl : Computable l) (hg : Computable g)
    (hf : Computable (fun p : α × β × σ => f p.1 p.2.1 p.2.2)) :
    Computable (fun a => (l a).foldr (f a) (g a)) := by
  refine (foldl_computable (l := fun a => (l a).reverse) (f := fun a s b => f a b s)
    (Computable.list_reverse.comp hl) hg
    (hf.comp (Computable.fst.pair ((Computable.snd.comp Computable.snd).pair
      (Computable.fst.comp Computable.snd))))).of_eq ?_
  intro a
  exact List.foldl_reverse

theorem foldl_concat {β σ : Type*} (h : β → σ) (l : List β) (c : List σ) :
    l.foldl (fun acc b => acc ++ [h b]) c = c ++ l.map h := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => simp [ih]

theorem map_computable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {l : α → List β} {f : α → β → σ}
    (hl : Computable l) (hf : Computable (fun p : α × β => f p.1 p.2)) :
    Computable (fun a => (l a).map (f a)) := by
  refine (foldl_computable (l := l) (g := fun _ => ([] : List σ))
    (f := fun a acc b => acc ++ [f a b]) hl (Computable.const [])
    (Computable.list_concat.comp (Computable.fst.comp Computable.snd)
      (hf.comp (Computable.fst.pair (Computable.snd.comp Computable.snd))))).of_eq ?_
  intro a
  rw [foldl_concat, List.nil_append]

theorem all_eq_foldr {β : Type*} (l : List β) (p : β → Bool) :
    l.all p = l.foldr (fun b acc => p b && acc) true := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

theorem any_eq_foldr {β : Type*} (l : List β) (p : β → Bool) :
    l.any p = l.foldr (fun b acc => p b || acc) false := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

theorem all_computable {α β : Type*} [Primcodable α] [Primcodable β]
    {l : α → List β} {p : α → β → Bool}
    (hl : Computable l) (hp : Computable (fun q : α × β => p q.1 q.2)) :
    Computable (fun a => (l a).all (p a)) := by
  refine (foldr_computable (f := fun a b acc => p a b && acc) hl (Computable.const true)
    (Primrec.and.to_comp.comp (hp.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd))).of_eq ?_
  intro a
  exact (all_eq_foldr _ _).symm

theorem any_computable {α β : Type*} [Primcodable α] [Primcodable β]
    {l : α → List β} {p : α → β → Bool}
    (hl : Computable l) (hp : Computable (fun q : α × β => p q.1 q.2)) :
    Computable (fun a => (l a).any (p a)) := by
  refine (foldr_computable (f := fun a b acc => p a b || acc) hl (Computable.const false)
    (Primrec.or.to_comp.comp (hp.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd))).of_eq ?_
  intro a
  exact (any_eq_foldr _ _).symm

theorem foldl_mul_eq {β M : Type*} [Monoid M] (h : β → M) (l : List β) (c : M) :
    l.foldl (fun acc x => acc * h x) c = c * (l.map h).prod := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => simp [ih, mul_assoc]

theorem foldl_add_eq {β M : Type*} [AddMonoid M] (h : β → M) (l : List β) (c : M) :
    l.foldl (fun acc x => acc + h x) c = c + (l.map h).sum := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

/-! ### Rational arithmetic -/

theorem rat_abs : Computable (fun q : ℚ => |q|) := by
  refine (Computable.cond (UpperCoding.rat_lt.decide.to_comp.comp Computable.id
    (Computable.const 0)) UpperCoding.rat_neg Computable.id).of_eq ?_
  intro q
  by_cases h : q < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.mp h)]

theorem rat_lt_computable {α : Type*} [Primcodable α] {f g : α → ℚ}
    (hf : Computable f) (hg : Computable g) : Computable (fun a => decide (f a < g a)) :=
  UpperCoding.rat_lt.decide.to_comp.comp hf hg

/-- The grid spacing `1/(k+1)`. -/
def step (k : ℕ) : ℚ := 1/((k:ℚ)+1)

theorem step_computable : Computable step := by
  refine (UpperCoding.rat_fraction.comp ((Computable.const (1:ℤ)).pair Computable.id)).of_eq ?_
  intro k
  simp [step]

theorem step_pos (k : ℕ) : (0:ℝ) < (step k : ℝ) := by
  simp only [step]; push_cast; positivity

theorem step_antitone (k : ℕ) : ((step (k+1) : ℚ) : ℝ) ≤ (step k : ℝ) := by
  simp only [step]; push_cast
  apply one_div_le_one_div_of_le (by positivity)
  linarith

/-! ### Exact evaluation at rational points -/

def gval (g : List ℚ) (i : ℕ) : ℝ := ((g.getD i 0 : ℚ) : ℝ)
def factorQ (g : List ℚ) : Factor → ℚ := Sum.elim (fun q => q) (fun i => g.getD i 0)
def monoQ (g : List ℚ) (m : List Factor) : ℚ := m.foldl (fun acc f => acc * factorQ g f) 1
def evalQ (g : List ℚ) (p : Poly) : ℚ := p.foldl (fun acc m => acc + monoQ g m) 0

theorem factorQ_primrec : Primrec (fun q : List ℚ × Factor => factorQ q.1 q.2) := by
  refine (Primrec.sumCasesOn (g := fun (_ : List ℚ × Factor) (c : ℚ) => c)
    (h := fun (q : List ℚ × Factor) (i : ℕ) => q.1.getD i 0) Primrec.snd Primrec.snd
    ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).of_eq ?_
  rintro ⟨g, f | i⟩ <;> rfl

/- Compositions below are elaborated without an expected type and only then matched,
so that unification never has to guess an inner function under a projection. -/
theorem monoQ_computable : Computable (fun q : List ℚ × List Factor => monoQ q.1 q.2) := by
  have hpair : Computable (fun p : (List ℚ × List Factor) × ℚ × Factor => (p.1.1, p.2.2)) :=
    (Computable.fst.comp Computable.fst).pair (Computable.snd.comp Computable.snd)
  have hacc : Computable (fun p : (List ℚ × List Factor) × ℚ × Factor => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hfac := factorQ_primrec.to_comp.comp hpair
  have hf := UpperCoding.rat_mul.comp hacc hfac
  exact (foldl_computable (l := fun q : List ℚ × List Factor => q.2) (g := fun _ => (1:ℚ))
    (f := fun q acc f => acc * factorQ q.1 f) Computable.snd (Computable.const 1) hf).of_eq
      (fun _ => rfl)

theorem evalQ_computable : Computable (fun q : List ℚ × Poly => evalQ q.1 q.2) := by
  have hpair : Computable (fun p : (List ℚ × Poly) × ℚ × List Factor => (p.1.1, p.2.2)) :=
    (Computable.fst.comp Computable.fst).pair (Computable.snd.comp Computable.snd)
  have hacc : Computable (fun p : (List ℚ × Poly) × ℚ × List Factor => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hm := monoQ_computable.comp hpair
  have hf := UpperCoding.rat_add.comp hacc hm
  exact (foldl_computable (l := fun q : List ℚ × Poly => q.2) (g := fun _ => (0:ℚ))
    (f := fun q acc m => acc + monoQ q.1 m) Computable.snd (Computable.const 0) hf).of_eq
      (fun _ => rfl)

theorem cast_monoQ (g : List ℚ) (m : List Factor) :
    ((monoQ g m : ℚ) : ℝ) = (m.map (factorEval (gval g))).prod := by
  rw [monoQ, foldl_mul_eq, one_mul, Rat.cast_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro f _
  cases f <;> simp [factorQ, factorEval, gval]

theorem cast_evalQ (g : List ℚ) (p : Poly) : ((evalQ g p : ℚ) : ℝ) = eval (gval g) p := by
  rw [evalQ, foldl_add_eq, zero_add, Rat.cast_list_sum, List.map_map, eval]
  congr 1
  apply List.map_congr_left
  intro m _
  simp [cast_monoQ]

/-! ### Lipschitz bounds on a box -/

/-- Bound for a factor's modulus on the box `[-B,B]`. -/
def fM (B : ℕ) : Factor → ℚ := Sum.elim (fun q => |q|) (fun _ => (B:ℚ))
/-- Lipschitz constant of a factor in the sup norm. -/
def fD : Factor → ℚ := Sum.elim (fun _ => 0) (fun _ => 1)
/-- Modulus bound and sup-norm Lipschitz constant of a monomial on `[-B,B]`. -/
def monoLip (B : ℕ) (m : List Factor) : ℚ × ℚ :=
  m.foldr (fun f acc => (fM B f * acc.1, fM B f * acc.2 + fD f * acc.1)) (1, 0)
/-- Sup-norm Lipschitz constant of a polynomial on `[-B,B]`. -/
def polyLip (B : ℕ) (p : Poly) : ℚ := p.foldl (fun acc m => acc + (monoLip B m).2) 0

theorem monoLip_cons (B : ℕ) (f : Factor) (m : List Factor) :
    monoLip B (f :: m) = (fM B f * (monoLip B m).1,
      fM B f * (monoLip B m).2 + fD f * (monoLip B m).1) := rfl

theorem fM_nonneg (B : ℕ) (f : Factor) : (0:ℚ) ≤ fM B f := by
  cases f <;> simp [fM]
theorem fD_nonneg (f : Factor) : (0:ℚ) ≤ fD f := by
  cases f <;> simp [fD]

theorem monoLip_nonneg (B : ℕ) (m : List Factor) :
    0 ≤ (monoLip B m).1 ∧ 0 ≤ (monoLip B m).2 := by
  induction m with
  | nil => simp [monoLip]
  | cons f m ih =>
    rw [monoLip_cons]
    exact ⟨mul_nonneg (fM_nonneg B f) ih.1,
      add_nonneg (mul_nonneg (fM_nonneg B f) ih.2) (mul_nonneg (fD_nonneg f) ih.1)⟩

theorem polyLip_eq (B : ℕ) (p : Poly) : polyLip B p = (p.map fun m => (monoLip B m).2).sum := by
  rw [polyLip, foldl_add_eq, zero_add]

theorem polyLip_nonneg (B : ℕ) (p : Poly) : 0 ≤ polyLip B p := by
  rw [polyLip_eq]
  apply List.sum_nonneg
  intro x hx
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
  exact (monoLip_nonneg B m).2

theorem mono_bound (B : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (v w : ℕ → ℝ) (m : List Factor)
    (hv : ∀ i, Sum.inr i ∈ m → |v i| ≤ B) (hw : ∀ i, Sum.inr i ∈ m → |w i| ≤ B)
    (hvw : ∀ i, Sum.inr i ∈ m → |v i - w i| ≤ δ) :
    |(m.map (factorEval v)).prod| ≤ ((monoLip B m).1 : ℝ) ∧
      |(m.map (factorEval w)).prod| ≤ ((monoLip B m).1 : ℝ) ∧
      |(m.map (factorEval v)).prod - (m.map (factorEval w)).prod| ≤
        ((monoLip B m).2 : ℝ) * δ := by
  induction m with
  | nil => simp [monoLip]
  | cons f m ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hv i (List.mem_cons_of_mem _ hi))
      (fun i hi => hw i (List.mem_cons_of_mem _ hi)) (fun i hi => hvw i (List.mem_cons_of_mem _ hi))
    have hf : |factorEval v f| ≤ (fM B f : ℝ) ∧ |factorEval w f| ≤ (fM B f : ℝ) ∧
        |factorEval v f - factorEval w f| ≤ (fD f : ℝ) * δ := by
      cases f with
      | inl q => simp [factorEval, fM, fD]
      | inr i =>
        simp only [factorEval, fM, fD, Sum.elim_inr, Rat.cast_natCast, Rat.cast_one, one_mul]
        exact ⟨hv i (by simp), hw i (by simp), hvw i (by simp)⟩
    have hMf : (0:ℝ) ≤ (fM B f : ℝ) := by exact_mod_cast fM_nonneg B f
    have hDf : (0:ℝ) ≤ (fD f : ℝ) := by exact_mod_cast fD_nonneg f
    have hM : (0:ℝ) ≤ ((monoLip B m).1 : ℝ) := by exact_mod_cast (monoLip_nonneg B m).1
    rw [monoLip_cons, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
    push_cast
    set a := factorEval v f
    set a' := factorEval w f
    set P := (m.map (factorEval v)).prod
    set P' := (m.map (factorEval w)).prod
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_mul]
      exact mul_le_mul hf.1 h1 (abs_nonneg _) hMf
    · rw [abs_mul]
      exact mul_le_mul hf.2.1 h2 (abs_nonneg _) hMf
    · calc |a * P - a' * P'| = |a * (P - P') + (a - a') * P'| := by ring_nf
        _ ≤ |a * (P - P')| + |(a - a') * P'| := abs_add_le _ _
        _ = |a| * |P - P'| + |a - a'| * |P'| := by rw [abs_mul, abs_mul]
        _ ≤ (fM B f : ℝ) * (((monoLip B m).2 : ℝ) * δ) + ((fD f : ℝ) * δ) * ((monoLip B m).1 : ℝ) :=
            add_le_add (mul_le_mul hf.1 h3 (abs_nonneg _) hMf)
              (mul_le_mul hf.2.2 h2 (abs_nonneg _) (mul_nonneg hDf hδ))
        _ = ((fM B f : ℝ) * ((monoLip B m).2 : ℝ) + (fD f : ℝ) * ((monoLip B m).1 : ℝ)) * δ := by
            ring

theorem poly_bound_aux (B : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (v w : ℕ → ℝ) (p : Poly)
    (hv : ∀ m ∈ p, ∀ i, Sum.inr i ∈ m → |v i| ≤ B) (hw : ∀ m ∈ p, ∀ i, Sum.inr i ∈ m → |w i| ≤ B)
    (hvw : ∀ m ∈ p, ∀ i, Sum.inr i ∈ m → |v i - w i| ≤ δ) :
    |eval v p - eval w p| ≤ ((p.map fun m => ((monoLip B m).2 : ℝ))).sum * δ := by
  induction p with
  | nil => simp [eval]
  | cons m p ih =>
    have h1 := (mono_bound B δ hδ v w m (hv m (by simp)) (hw m (by simp)) (hvw m (by simp))).2.2
    have h2 := ih (fun m hm => hv m (List.mem_cons_of_mem _ hm))
      (fun m hm => hw m (List.mem_cons_of_mem _ hm)) (fun m hm => hvw m (List.mem_cons_of_mem _ hm))
    simp only [eval, List.map_cons, List.sum_cons] at h2 ⊢
    calc _ ≤ |(m.map (factorEval v)).prod - (m.map (factorEval w)).prod| +
          |((p.map fun m => (m.map (factorEval v)).prod)).sum -
            ((p.map fun m => (m.map (factorEval w)).prod)).sum| := by
          rw [show ∀ x y z u : ℝ, (x + y) - (z + u) = (x - z) + (y - u) by intros; ring]
          exact abs_add_le _ _
      _ ≤ ((monoLip B m).2 : ℝ) * δ + ((p.map fun m => ((monoLip B m).2 : ℝ))).sum * δ :=
          add_le_add h1 h2
      _ = _ := by ring

theorem poly_bound (B : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (v w : ℕ → ℝ) (p : Poly)
    (hv : ∀ m ∈ p, ∀ i, Sum.inr i ∈ m → |v i| ≤ B) (hw : ∀ m ∈ p, ∀ i, Sum.inr i ∈ m → |w i| ≤ B)
    (hvw : ∀ m ∈ p, ∀ i, Sum.inr i ∈ m → |v i - w i| ≤ δ) :
    |eval v p - eval w p| ≤ (polyLip B p : ℝ) * δ := by
  have hL : (polyLip B p : ℝ) = ((p.map fun m => ((monoLip B m).2 : ℝ))).sum := by
    rw [polyLip_eq, Rat.cast_list_sum, List.map_map]
    rfl
  rw [hL]
  exact poly_bound_aux B δ hδ v w p hv hw hvw

theorem fM_computable : Computable (fun q : ℕ × Factor => fM q.1 q.2) := by
  refine (Computable.sumCasesOn (g := fun (_ : ℕ × Factor) (c : ℚ) => |c|)
    (h := fun (q : ℕ × Factor) (_ : ℕ) => (q.1:ℚ)) Computable.snd
    (rat_abs.comp Computable.snd).to₂
    (UpperCoding.rat_natCast.comp (Computable.fst.comp Computable.fst)).to₂).of_eq ?_
  rintro ⟨B, f | i⟩ <;> rfl

theorem fD_computable : Computable fD := by
  refine (Computable.sumCasesOn (g := fun (_ : Factor) (_ : ℚ) => (0:ℚ))
    (h := fun (_ : Factor) (_ : ℕ) => (1:ℚ)) Computable.id
    (Computable.const 0) (Computable.const 1)).of_eq ?_
  rintro (f | i) <;> rfl

theorem monoLip_computable : Computable (fun q : ℕ × List Factor => monoLip q.1 q.2) := by
  have hBf : Computable (fun p : (ℕ × List Factor) × Factor × (ℚ × ℚ) => (p.1.1, p.2.1)) :=
    (Computable.fst.comp Computable.fst).pair (Computable.fst.comp Computable.snd)
  have hf0 : Computable (fun p : (ℕ × List Factor) × Factor × (ℚ × ℚ) => p.2.1) :=
    Computable.fst.comp Computable.snd
  have h1 : Computable (fun p : (ℕ × List Factor) × Factor × (ℚ × ℚ) => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have h2 : Computable (fun p : (ℕ × List Factor) × Factor × (ℚ × ℚ) => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hM := fM_computable.comp hBf
  have hD := fD_computable.comp hf0
  have hA := UpperCoding.rat_mul.comp hM h1
  have hB := UpperCoding.rat_add.comp (UpperCoding.rat_mul.comp hM h2) (UpperCoding.rat_mul.comp hD h1)
  exact (foldr_computable (l := fun q : ℕ × List Factor => q.2) (g := fun _ => ((1:ℚ), (0:ℚ)))
    (f := fun q f acc => (fM q.1 f * acc.1, fM q.1 f * acc.2 + fD f * acc.1)) Computable.snd
    (Computable.const _) (hA.pair hB)).of_eq (fun _ => rfl)

theorem polyLip_computable : Computable (fun q : ℕ × Poly => polyLip q.1 q.2) := by
  have hpair : Computable (fun p : (ℕ × Poly) × ℚ × List Factor => (p.1.1, p.2.2)) :=
    (Computable.fst.comp Computable.fst).pair (Computable.snd.comp Computable.snd)
  have hacc : Computable (fun p : (ℕ × Poly) × ℚ × List Factor => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hm := Computable.snd.comp (monoLip_computable.comp hpair)
  have hf := UpperCoding.rat_add.comp hacc hm
  exact (foldl_computable (l := fun q : ℕ × Poly => q.2) (g := fun _ => (0:ℚ))
    (f := fun q acc m => acc + (monoLip q.1 m).2) Computable.snd (Computable.const 0) hf).of_eq
      (fun _ => rfl)

/-! ### Grids -/

def gridVals (B k : ℕ) : List ℚ :=
  (List.range (2*B*(k+1)+1)).map fun j : ℕ => (j:ℚ)*step k - B

def gridPoints (V : List ℚ) (N : ℕ) : List (List ℚ) :=
  Nat.rec (motive := fun _ => List (List ℚ)) [[]]
    (fun _ acc => acc.flatMap fun g => V.map fun x => x :: g) N

theorem mem_gridPoints (V : List ℚ) (N : ℕ) (g : List ℚ) :
    g ∈ gridPoints V N ↔ g.length = N ∧ ∀ x ∈ g, x ∈ V := by
  induction N generalizing g with
  | zero =>
    change g ∈ [[]] ↔ _
    cases g with
    | nil => simp
    | cons x g => simp
  | succ N ih =>
    change g ∈ (gridPoints V N).flatMap (fun g => V.map fun x => x :: g) ↔ _
    rw [List.mem_flatMap]
    cases g with
    | nil => simp
    | cons x g =>
      constructor
      · rintro ⟨g', hg', hx⟩
        obtain ⟨y, hy, he⟩ := List.mem_map.mp hx
        obtain ⟨rfl, rfl⟩ := List.cons.inj he
        obtain ⟨hl, hm⟩ := (ih g').mp hg'
        refine ⟨by simp [hl], ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hy
        · exact hm z hz
      · rintro ⟨hl, hm⟩
        refine ⟨g, (ih g).mpr ⟨by simpa using hl, fun z hz => hm z (by simp [hz])⟩, ?_⟩
        exact List.mem_map.mpr ⟨x, hm x (by simp), rfl⟩

theorem gridVals_computable : Computable (fun q : ℕ × ℕ => gridVals q.1 q.2) := by
  have hlen : Computable (fun q : ℕ × ℕ => 2*q.1*(q.2+1)+1) :=
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
      (Primrec.succ.comp Primrec.snd))).to_comp
  have hj : Computable (fun p : (ℕ × ℕ) × ℕ => p.2) := Computable.snd
  have hk : Computable (fun p : (ℕ × ℕ) × ℕ => p.1.2) := Computable.snd.comp Computable.fst
  have hB : Computable (fun p : (ℕ × ℕ) × ℕ => p.1.1) := Computable.fst.comp Computable.fst
  have hf := UpperCoding.rat_add.comp
      (UpperCoding.rat_mul.comp (UpperCoding.rat_natCast.comp hj) (step_computable.comp hk))
      (UpperCoding.rat_neg.comp (UpperCoding.rat_natCast.comp hB))
  have hl := Primrec.list_range.to_comp.comp hlen
  refine (map_computable (l := fun q : ℕ × ℕ => List.range (2*q.1*(q.2+1)+1))
    (f := fun q (j : ℕ) => (j:ℚ)*step q.2 + -(q.1:ℚ)) hl hf).of_eq ?_
  intro q
  simp only [gridVals, sub_eq_add_neg]

theorem gridPoints_primrec : Primrec (fun q : List ℚ × ℕ => gridPoints q.1 q.2) := by
  have hstep : Primrec (fun r : (List ℚ × ℕ) × ℕ × List (List ℚ) =>
      r.2.2.flatMap fun g => r.1.1.map fun x => x :: g) :=
    Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to₂
  exact Primrec.nat_rec' Primrec.snd (Primrec.const [[]]) hstep.to₂

theorem gridVals_bound (B k : ℕ) (x : ℚ) (hx : x ∈ gridVals B k) : |(x:ℝ)| ≤ B := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  have hj' : (j:ℝ) ≤ 2*B*(k+1) := by
    have := List.mem_range.mp hj
    exact_mod_cast Nat.lt_succ_iff.mp this
  have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
  simp only [step]
  push_cast
  rw [abs_le]
  constructor
  · have : (0:ℝ) ≤ (j:ℝ) * (1/((k:ℝ)+1)) := by positivity
    linarith
  · have : (j:ℝ) * (1/((k:ℝ)+1)) ≤ 2*B := by
      rw [mul_one_div, div_le_iff₀ hk]
      linarith
    linarith

theorem near_exists (B k : ℕ) (x : ℝ) (hx : |x| ≤ B) :
    ∃ q ∈ gridVals B k, |x - (q:ℝ)| ≤ (step k : ℝ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
  have h0 : 0 ≤ (x + B) * ((k:ℝ)+1) := mul_nonneg (by linarith) hk.le
  set j := ⌊(x + B) * ((k:ℝ)+1)⌋₊
  have hj1 : (j:ℝ) ≤ (x + B) * ((k:ℝ)+1) := Nat.floor_le h0
  have hj2 : (x + B) * ((k:ℝ)+1) < j + 1 := Nat.lt_floor_add_one _
  have hjle : j ≤ 2*B*(k+1) := by
    have : (j:ℝ) ≤ ((2*B*(k+1) : ℕ) : ℝ) := by
      push_cast
      calc (j:ℝ) ≤ (x + B) * ((k:ℝ)+1) := hj1
        _ ≤ (2*B) * ((k:ℝ)+1) := mul_le_mul_of_nonneg_right (by linarith) hk.le
        _ = 2*B*((k:ℝ)+1) := by ring
    exact_mod_cast this
  refine ⟨(j:ℚ)*step k - B, List.mem_map.mpr ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le hjle), rfl⟩, ?_⟩
  simp only [step]
  push_cast
  have hkey : x - ((j:ℝ) * (1/((k:ℝ)+1)) - B) = ((x + B) * ((k:ℝ)+1) - j) / ((k:ℝ)+1) := by
    field_simp
    ring
  rw [hkey, abs_le]
  constructor
  · have : 0 ≤ ((x + B) * ((k:ℝ)+1) - j) / ((k:ℝ)+1) := div_nonneg (by linarith) hk.le
    have : (0:ℝ) ≤ 1/((k:ℝ)+1) := by positivity
    linarith
  · rw [div_le_div_iff_of_pos_right hk]
    linarith

/-! ### The certificate -/

def nvars (s : Sentence) : ℕ := (freeVars s).foldr max 0 + 1

theorem le_foldr_max (l : List ℕ) (i : ℕ) (h : i ∈ l) : i ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem mem_freeVars (s : Sentence) (a : Atom) (ha : a ∈ s) (m : List Factor) (hm : m ∈ a.2)
    (i : ℕ) (hi : Sum.inr i ∈ m) : i ∈ freeVars s := by
  simp only [freeVars, List.mem_flatMap, List.mem_filterMap]
  exact ⟨a, ha, m, hm, Sum.inr i, hi, rfl⟩

theorem lt_nvars (s : Sentence) (a : Atom) (ha : a ∈ s) (m : List Factor) (hm : m ∈ a.2)
    (i : ℕ) (hi : Sum.inr i ∈ m) : i < nvars s :=
  Nat.lt_succ_of_le (le_foldr_max _ _ (mem_freeVars s a ha m hm i hi))

theorem getRight_primrec : Primrec (fun f : Factor => f.getRight?) := by
  refine (Primrec.sumCasesOn (g := fun (_ : Factor) (_ : ℚ) => (none : Option ℕ))
    (h := fun (_ : Factor) (i : ℕ) => some i) Primrec.id (Primrec.const none)
    (Primrec.option_some.comp Primrec.snd)).of_eq ?_
  rintro (q | i) <;> rfl

theorem freeVars_primrec : Primrec freeVars := by
  unfold freeVars
  exact Primrec.list_flatMap Primrec.id
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (Primrec.listFilterMap Primrec.snd (getRight_primrec.comp Primrec.snd).to₂).to₂).to₂

theorem nvars_primrec : Primrec nvars := by
  refine (Primrec.succ.comp (Primrec.list_foldr freeVars_primrec (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)).of_eq ?_
  intro s
  rfl

/-- The atom is violated at the grid point by more than its Lipschitz slack. -/
def robust (B k : ℕ) (g : List ℚ) (a : Atom) : Bool :=
  cond a.1 (decide (polyLip B a.2 * step k < |evalQ g a.2|))
    (decide (evalQ g a.2 < -(polyLip B a.2 * step k)))

/-- Rational emptiness certificate for the bounded sentence at resolution `k`. -/
def cert (x : Sentence × ℕ × ℕ) : Bool :=
  (gridPoints (gridVals x.2.1 x.2.2) (nvars x.1)).all fun g => x.1.any fun a => robust x.2.1 x.2.2 g a

theorem robust_computable : Computable (fun q : (ℕ × ℕ × List ℚ) × Atom =>
    robust q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have hBp : Computable (fun q : (ℕ × ℕ × List ℚ) × Atom => (q.1.1, q.2.2)) :=
    (Computable.fst.comp Computable.fst).pair (Computable.snd.comp Computable.snd)
  have hk : Computable (fun q : (ℕ × ℕ × List ℚ) × Atom => q.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hgp : Computable (fun q : (ℕ × ℕ × List ℚ) × Atom => (q.1.2.2, q.2.2)) :=
    (Computable.snd.comp (Computable.snd.comp Computable.fst)).pair (Computable.snd.comp Computable.snd)
  have hL := UpperCoding.rat_mul.comp (polyLip_computable.comp hBp) (step_computable.comp hk)
  have hE := evalQ_computable.comp hgp
  have hb : Computable (fun q : (ℕ × ℕ × List ℚ) × Atom => q.2.1) :=
    Computable.fst.comp Computable.snd
  have h1 := rat_lt_computable hL (rat_abs.comp hE)
  have h2 := rat_lt_computable hE (UpperCoding.rat_neg.comp hL)
  exact (Computable.cond hb h1 h2).of_eq (fun _ => rfl)

theorem cert_computable : Computable cert := by
  have hs : Computable (fun x : Sentence × ℕ × ℕ => x.1) := Computable.fst
  have hBk : Computable (fun x : Sentence × ℕ × ℕ => x.2) := Computable.snd
  have hV := gridVals_computable.comp hBk
  have hN := nvars_primrec.to_comp.comp hs
  have hP := gridPoints_primrec.to_comp.comp (hV.pair hN)
  have hsel : Computable (fun q : ((Sentence × ℕ × ℕ) × List ℚ) × Atom =>
      ((q.1.1.2.1, q.1.1.2.2, q.1.2), q.2)) :=
    ((Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
      ((Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
        (Computable.snd.comp Computable.fst))).pair Computable.snd
  have hR := robust_computable.comp hsel
  have hl : Computable (fun q : (Sentence × ℕ × ℕ) × List ℚ => q.1.1) :=
    Computable.fst.comp Computable.fst
  have hA := any_computable (l := fun q : (Sentence × ℕ × ℕ) × List ℚ => q.1.1)
    (p := fun q a => robust q.1.2.1 q.1.2.2 q.2 a) hl hR
  exact (all_computable
    (l := fun x : Sentence × ℕ × ℕ => gridPoints (gridVals x.2.1 x.2.2) (nvars x.1))
    (p := fun x g => x.1.any fun a => robust x.2.1 x.2.2 g a) hP hA).of_eq (fun _ => rfl)

/-! ### Soundness and completeness -/

/-- Truth with every coordinate of the valuation in `[-B,B]`. -/
def BoxTruth (B : ℕ) (s : Sentence) : Prop :=
  ∃ v : ℕ → ℝ, (∀ i, |v i| ≤ B) ∧ ∀ a ∈ s, holds v a

theorem gval_bound (B k N : ℕ) (g : List ℚ) (hg : g ∈ gridPoints (gridVals B k) N) (i : ℕ) :
    |gval g i| ≤ B := by
  obtain ⟨_, hm⟩ := (mem_gridPoints _ _ _).mp hg
  unfold gval
  rw [List.getD_eq_getElem?_getD]
  cases h : g[i]? with
  | none => simp
  | some x => simpa using gridVals_bound B k x (hm x (List.mem_of_getElem? h))

theorem cert_sound (s : Sentence) (B k : ℕ) (h : cert (s,B,k) = true) : ¬ BoxTruth B s := by
  rintro ⟨v, hv, hs⟩
  choose q hq hqd using fun i => near_exists B k (v i) (hv i)
  let g := (List.range (nvars s)).map q
  have hg : g ∈ gridPoints (gridVals B k) (nvars s) := by
    refine (mem_gridPoints _ _ _).mpr ⟨by simp [g], ?_⟩
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hq i
  have hgv (i : ℕ) (hi : i < nvars s) : gval g i = q i := by
    simp [gval, g, List.getD_eq_getElem?_getD, List.getElem?_range hi]
  have h' : (gridPoints (gridVals B k) (nvars s)).all
      (fun g => s.any fun a => robust B k g a) = true := h
  have hall := List.all_eq_true.mp h' g hg
  obtain ⟨a, ha, hr⟩ := List.any_eq_true.mp hall
  have hvars : ∀ m ∈ a.2, ∀ i, Sum.inr i ∈ m → i < nvars s :=
    fun m hm i hi => lt_nvars s a ha m hm i hi
  have hb := poly_bound B (step k : ℝ) (step_pos k).le v (gval g) a.2
    (fun m _ i _ => hv i) (fun m _ i _ => gval_bound B k _ g hg i)
    (fun m hm i hi => by rw [hgv i (hvars m hm i hi)]; exact hqd i)
  have hev := cast_evalQ g a.2
  have hva := hs a ha
  rcases a with ⟨b, p⟩
  cases b with
  | true =>
    simp only [robust, Bool.cond_true, decide_eq_true_eq] at hr
    have hr' : ((polyLip B p * step k : ℚ) : ℝ) < ((|evalQ g p| : ℚ) : ℝ) := by exact_mod_cast hr
    push_cast at hr'
    rw [hev] at hr'
    simp only [holds, ↓reduceIte] at hva
    rw [hva, zero_sub, abs_neg] at hb
    linarith
  | false =>
    simp only [robust, Bool.cond_false, decide_eq_true_eq] at hr
    have hr' : ((evalQ g p : ℚ) : ℝ) < ((-(polyLip B p * step k) : ℚ) : ℝ) := by exact_mod_cast hr
    push_cast at hr'
    rw [hev] at hr'
    simp only [holds, Bool.false_eq_true, ↓reduceIte] at hva
    have := (abs_le.mp hb).2
    linarith

/-- Signed violation of an atom: nonpositive exactly when the atom holds. -/
noncomputable def viol (v : ℕ → ℝ) (a : Atom) : ℝ := if a.1 then |eval v a.2| else -eval v a.2

theorem eval_continuous (p : Poly) : Continuous (fun v : ℕ → ℝ => eval v p) := by
  unfold eval
  apply continuous_list_sum
  intro m _
  apply continuous_list_prod
  intro f _
  cases f with
  | inl q => exact continuous_const
  | inr i => exact continuous_apply i

theorem viol_continuous (a : Atom) : Continuous (fun v : ℕ → ℝ => viol v a) := by
  rcases a with ⟨b, p⟩
  cases b
  · simp only [viol, Bool.false_eq_true, ↓reduceIte]
    exact (eval_continuous p).neg
  · simp only [viol, ↓reduceIte]
    exact (eval_continuous p).abs

theorem holds_of_viol (v : ℕ → ℝ) (a : Atom) (L : ℝ)
    (h : ∀ k : ℕ, viol v a ≤ L * (step k : ℝ)) : holds v a := by
  have hle : viol v a ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨k, hk⟩ := exists_nat_gt (L / viol v a)
    have h1 := h k
    simp only [step] at h1
    push_cast at h1
    have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
    rw [div_lt_iff₀ hpos] at hk
    have : L * (1/((k:ℝ)+1)) < viol v a := by
      rw [mul_one_div, div_lt_iff₀ hk1]
      nlinarith
    linarith
  rcases a with ⟨b, p⟩
  cases b
  · simp only [viol, Bool.false_eq_true, ↓reduceIte] at hle
    simp only [holds, Bool.false_eq_true, ↓reduceIte]
    linarith
  · simp only [viol, ↓reduceIte] at hle
    simp only [holds, ↓reduceIte]
    exact abs_nonpos_iff.mp hle

theorem cert_complete (s : Sentence) (B : ℕ) (h : ∀ k, cert (s,B,k) = false) : BoxTruth B s := by
  let K : Set (ℕ → ℝ) := {v | ∀ i, |v i| ≤ B}
  have hKc : IsCompact K := by
    have he : K = Set.Icc (fun _ => -(B:ℝ)) (fun _ => (B:ℝ)) := by
      ext v
      simp only [K, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def, abs_le, forall_and]
    rw [he]
    exact isCompact_Icc
  let t : ℕ → Set (ℕ → ℝ) := fun k =>
    K ∩ {v | ∀ a ∈ s, viol v a ≤ (polyLip B a.2 : ℝ) * (step k : ℝ)}
  have hclosed (k : ℕ) : IsClosed {v : ℕ → ℝ | ∀ a ∈ s, viol v a ≤ (polyLip B a.2 : ℝ) * (step k : ℝ)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun _ =>
      isClosed_le (viol_continuous a) continuous_const
  have htd (k : ℕ) : t (k+1) ⊆ t k := by
    rintro v ⟨hK, hv⟩
    refine ⟨hK, fun a ha => (hv a ha).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (step_antitone k) (by exact_mod_cast polyLip_nonneg B a.2)
  have htn (k : ℕ) : (t k).Nonempty := by
    have hk := h k
    have hn : ¬ ((gridPoints (gridVals B k) (nvars s)).all
        (fun g => s.any fun a => robust B k g a) = true) := by
      change ¬ (cert (s,B,k) = true)
      rw [hk]
      decide
    rw [List.all_eq_true] at hn
    push Not at hn
    obtain ⟨g, hg, hng⟩ := hn
    refine ⟨gval g, fun i => gval_bound B k _ g hg i, ?_⟩
    intro a ha
    have hr : robust B k g a = false := by
      by_contra hc
      exact hng (List.any_eq_true.mpr ⟨a, ha, by simpa using hc⟩)
    have hev := cast_evalQ g a.2
    rcases a with ⟨b, p⟩
    cases b with
    | true =>
      simp only [robust, Bool.cond_true, decide_eq_false_iff_not, not_lt] at hr
      have hr' : ((|evalQ g p| : ℚ) : ℝ) ≤ ((polyLip B p * step k : ℚ) : ℝ) := by exact_mod_cast hr
      push_cast at hr'
      rw [hev] at hr'
      simpa [viol] using hr'
    | false =>
      simp only [robust, Bool.cond_false, decide_eq_false_iff_not, not_lt] at hr
      have hr' : ((-(polyLip B p * step k) : ℚ) : ℝ) ≤ ((evalQ g p : ℚ) : ℝ) := by exact_mod_cast hr
      push_cast at hr'
      rw [hev] at hr'
      simp only [viol, Bool.false_eq_true, ↓reduceIte]
      linarith
  have ht0 : IsCompact (t 0) := hKc.inter_right (hclosed 0)
  have hKcl : IsClosed K := hKc.isClosed
  obtain ⟨v, hv⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0
    (fun k => hKcl.inter (hclosed k))
  rw [Set.mem_iInter] at hv
  refine ⟨v, (hv 0).1, fun a ha => ?_⟩
  exact holds_of_viol v a _ (fun k => (hv k).2 a ha)

/-- Bounded truth is uniformly co-semidecidable by exact rational certificates. -/
theorem boxTruth_iff_cert (s : Sentence) (B : ℕ) : BoxTruth B s ↔ ∀ k, cert (s,B,k) = false := by
  constructor
  · intro hb k
    cases hc : cert (s,B,k)
    · rfl
    · exact absurd hb (cert_sound s B k hc)
  · exact cert_complete s B

theorem boxTruth_piOne : PiOne (fun x : Sentence × ℕ => BoxTruth x.2 x.1) := by
  refine ⟨fun q => !cert (q.1.1, q.1.2, q.2),
    Primrec.not.to_comp.comp (cert_computable.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd))), ?_⟩
  intro x
  dsimp only
  rw [boxTruth_iff_cert]
  simp

end Sigma2.UpperGridCertificate
