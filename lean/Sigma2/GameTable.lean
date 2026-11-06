import Sigma2.Statements

noncomputable section
open scoped BigOperators
namespace Sigma2.GameTable

/-- A finite rectangular table in the same row-major convention as RawGame. -/
def table {α : Type} {A B : ℕ} (hB : 0 < B) (f : Fin A → Fin B → α) : List α :=
  List.ofFn (fun k : Fin (A*B) =>
    f ⟨k.val/B, (Nat.div_lt_iff_lt_mul hB).mpr (by simpa [Nat.mul_comm] using k.isLt)⟩
      ⟨k.val%B, Nat.mod_lt _ hB⟩)

@[simp] theorem table_length {α : Type} {A B : ℕ} (hB : 0 < B)
    (f : Fin A → Fin B → α) : (table hB f).length = A*B := by
  simp [table]

@[simp] theorem table_lookup {α : Type} {A B : ℕ} (hB : 0 < B)
    (f : Fin A → Fin B → α) (x : Fin A) (y : Fin B) :
    (table hB f)[x.val*B+y.val]? = some (f x y) := by
  have hi : x.val*B+y.val < A*B := by nlinarith [x.isLt,y.isLt]
  simp only [table, List.getElem?_ofFn, hi, dite_true]
  congr 2 <;> apply Fin.ext
  · change (x.val*B+y.val)/B=x.val
    rw [Nat.mul_comm x.val B, Nat.mul_add_div hB, Nat.div_eq_of_lt y.isLt, Nat.add_zero]
  · simp [Nat.add_mod, Nat.mod_eq_of_lt y.isLt]

def pairIndex {A B : ℕ} (x : Fin A) (y : Fin B) : Fin (A*B) :=
  ⟨x.val*B+y.val, by nlinarith [x.isLt,y.isLt]⟩

def first {A B : ℕ} (hB : 0 < B) (k : Fin (A*B)) : Fin A :=
  ⟨k.val/B, (Nat.div_lt_iff_lt_mul hB).mpr (by simpa [Nat.mul_comm] using k.isLt)⟩

def second {A B : ℕ} (hB : 0 < B) (k : Fin (A*B)) : Fin B :=
  ⟨k.val%B, Nat.mod_lt _ hB⟩

@[simp] theorem first_pair {A B : ℕ} (hB : 0 < B) (x : Fin A) (y : Fin B) :
    first hB (pairIndex x y) = x := by
  apply Fin.ext
  change (x.val*B+y.val)/B=x.val
  rw [Nat.mul_comm x.val B, Nat.mul_add_div hB, Nat.div_eq_of_lt y.isLt, Nat.add_zero]

@[simp] theorem second_pair {A B : ℕ} (hB : 0 < B) (x : Fin A) (y : Fin B) :
    second hB (pairIndex x y) = y := by
  apply Fin.ext
  simp [second,pairIndex,Nat.add_mod,Nat.mod_eq_of_lt y.isLt]

def table4 {α : Type} {A B C D : ℕ} (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (f : Fin A → Fin B → Fin C → Fin D → α) : List α :=
  table (Nat.mul_pos hC hD) (fun xy ab =>
    f (first hB xy) (second hB xy) (first hD ab) (second hD ab))

@[simp] theorem table4_length {α : Type} {A B C D : ℕ}
    (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (f : Fin A → Fin B → Fin C → Fin D → α) :
    (table4 hB hC hD f).length = A*B*C*D := by
  simp [table4,Nat.mul_assoc]

@[simp] theorem table4_lookup {α : Type} {A B C D : ℕ}
    (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (f : Fin A → Fin B → Fin C → Fin D → α)
    (x : Fin A) (y : Fin B) (a : Fin C) (b : Fin D) :
    (table4 hB hC hD f)[((x.val*B+y.val)*C+a.val)*D+b.val]? = some (f x y a b) := by
  have hi : ((x.val*B+y.val)*C+a.val)*D+b.val =
      (pairIndex x y).val*(C*D)+(pairIndex a b).val := by dsimp [pairIndex]; ring
  rw [hi]
  simp only [table4,table_lookup,first_pair,second_pair]

/-- Exact row-major serialization into the existing game decoder. -/
def raw (G : Game) : RawGame :=
  (G.scenario,table (by omega) G.distribution,table4 (by omega) (by omega) (by omega) G.accepts)

@[simp] theorem distribution_lookup (G : Game) (x : QA G.scenario) (y : QB G.scenario) :
    rawDistribution (raw G) x y = G.distribution x y := by
  simp [rawDistribution,raw]

@[simp] theorem accepts_lookup (G : Game) (x : QA G.scenario) (y : QB G.scenario)
    (a : AA G.scenario) (b : BB G.scenario) :
    rawAccepts (raw G) x y a b = G.accepts x y a b := by
  simp [rawAccepts,raw]

theorem raw_valid (G : Game) : ValidRawGame (raw G) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [raw,table_length]
  · simp only [raw,table4_length]
  · intro x y; rw [distribution_lookup G x y]; exact G.distribution_nonneg x y
  · change (∑ x, ∑ y, rawDistribution (raw G) x y)=1
    calc
      _ = ∑ x : QA G.scenario, ∑ y : QB G.scenario, G.distribution x y := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        exact distribution_lookup G x y
      _ = 1 := G.distribution_sum

theorem gameOfRaw_eq (G : Game) (h : ValidRawGame (raw G)) : gameOfRaw (raw G) h = G := by
  have hd : rawDistribution (raw G) = G.distribution := by
    funext x y; exact distribution_lookup G x y
  have ha : rawAccepts (raw G) = G.accepts := by
    funext x y a b; exact accepts_lookup G x y a b
  cases G
  unfold gameOfRaw
  congr 1

def code (G : Game) : ℕ := Encodable.encode (raw G)

@[simp] theorem decode_code (G : Game) : decodeGame (code G) = some G := by
  simp [decodeGame,code,raw_valid,gameOfRaw_eq]

theorem game_codes_surjective (G : Game) : ∃ c,decodeGame c=some G :=
  ⟨code G,decode_code G⟩

#print axioms table_lookup
#print axioms table4_lookup
#print axioms raw_valid
#print axioms gameOfRaw_eq
#print axioms decode_code
#print axioms game_codes_surjective
end Sigma2.GameTable
