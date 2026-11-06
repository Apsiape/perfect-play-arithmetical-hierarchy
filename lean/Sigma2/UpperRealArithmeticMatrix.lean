import Sigma2.UpperRealArithmeticComplex
import Mathlib.Data.List.FinRange

namespace Sigma2.UpperRealArithmetic
noncomputable section
open scoped BigOperators ComplexOrder

structure Enumeration (ι : Type*) [Fintype ι] where
  entries : List ι
  mem : ∀ i, i ∈ entries
  sum_eq : ∀ f : ι → ℂ, (entries.map f).sum = ∑ i, f i

def enumFin (n : ℕ) : Enumeration (Fin n) where
  entries := List.finRange n
  mem _ := List.mem_finRange _
  sum_eq f := by simpa [← List.ofFn_eq_map] using (List.sum_ofFn (f := f))

def enumFixed (ι : Type*) [Fintype ι] : Enumeration ι := by
  classical
  exact ⟨Finset.univ.toList,by simp,by simp⟩

theorem sum_flatMap {α β : Type*} [AddMonoid β] (xs : List α) (f : α → List β) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

def enumProd {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : Enumeration ι) (F : Enumeration κ) : Enumeration (ι × κ) where
  entries := E.entries.flatMap fun i => F.entries.map fun j => (i,j)
  mem x := List.mem_flatMap.mpr ⟨x.1,E.mem _,List.mem_map.mpr ⟨x.2,F.mem _,rfl⟩⟩
  sum_eq f := by
    simp only [List.map_flatMap, sum_flatMap, List.map_map, Function.comp_def]
    simp_rw [F.sum_eq]
    rw [E.sum_eq,Fintype.sum_prod_type]

def all {ι : Type*} [Fintype ι] (E : Enumeration ι) (f : ι → Sentence) : Sentence :=
  E.entries.flatMap f

def total {ι : Type*} [Fintype ι] (E : Enumeration ι) (f : ι → CPoly) : CPoly :=
  csum (E.entries.map f)

@[simp] theorem models_all {ι : Type*} [Fintype ι] (v : ℕ → ℝ)
    (E : Enumeration ι) (f : ι → Sentence) : Models v (all E f) ↔ ∀ i, Models v (f i) := by
  simp only [all,models_flatMap]
  exact ⟨fun h i => h i (E.mem i),fun h i _ => h i⟩
@[simp] theorem ceval_total {ι : Type*} [Fintype ι] (v : ℕ → ℝ)
    (E : Enumeration ι) (f : ι → CPoly) : ceval v (total E f) = ∑ i, ceval v (f i) := by
  simp only [total,ceval_sum,List.map_map,Function.comp_def,E.sum_eq]

def evalMatrix {ι κ : Type*} (v : ℕ → ℝ) (X : Matrix ι κ CPoly) : Matrix ι κ ℂ :=
  fun i j => ceval v (X i j)
def gram {ι : Type*} [Fintype ι] (E : Enumeration ι) (Y : Matrix ι ι CPoly) : Matrix ι ι CPoly :=
  fun i j => total E fun k => cmul (cstar (Y k i)) (Y k j)
def matrixEq {ι : Type*} [Fintype ι] (E : Enumeration ι) (X Y : Matrix ι ι CPoly) : Sentence :=
  all E fun i => all E fun j => ceq (X i j) (Y i j)
def tr {ι : Type*} [Fintype ι] (E : Enumeration ι) (X : Matrix ι ι CPoly) : CPoly :=
  total E fun i => X i i

@[simp] theorem eval_gram {ι : Type*} [Fintype ι] (v : ℕ → ℝ)
    (E : Enumeration ι) (Y : Matrix ι ι CPoly) :
    evalMatrix v (gram E Y) = (evalMatrix v Y).conjTranspose * evalMatrix v Y := by
  funext i j
  simp [evalMatrix,gram,Matrix.mul_apply,Matrix.conjTranspose_apply]
@[simp] theorem models_matrixEq {ι : Type*} [Fintype ι] (v : ℕ → ℝ)
    (E : Enumeration ι) (X Y : Matrix ι ι CPoly) :
    Models v (matrixEq E X Y) ↔ evalMatrix v X = evalMatrix v Y := by
  simp only [matrixEq,models_all,models_ceq]
  constructor
  · intro h; funext i j; exact h i j
  · intro h i j; exact congrFun (congrFun h i) j
@[simp] theorem ceval_tr {ι : Type*} [Fintype ι] (v : ℕ → ℝ)
    (E : Enumeration ι) (X : Matrix ι ι CPoly) :
    ceval v (tr E X) = Matrix.trace (evalMatrix v X) := by
  simp [tr,Matrix.trace,evalMatrix]

/-- Simultaneously realize every complex variable indexed by an encodable type. -/
def valuation {α : Type*} [Encodable α] (z : α → ℂ) (k : ℕ) : ℝ :=
  let x := ((Encodable.decode (α := α) (k/2)).map z).getD 0
  if k % 2 = 0 then x.re else x.im

@[simp] theorem ceval_cvar_valuation {α : Type*} [Encodable α] (z : α → ℂ) (a : α) :
    ceval (valuation z) (cvar (Encodable.encode a)) = z a := by
  have hd : (2*Encodable.encode a+1)/2 = Encodable.encode a := by omega
  apply Complex.ext <;> simp [ceval,cvar,valuation,Encodable.encodek,hd]

end
end Sigma2.UpperRealArithmetic
