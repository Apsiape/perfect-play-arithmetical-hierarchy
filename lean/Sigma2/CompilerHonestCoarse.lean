import Sigma2.CompilerHonestCommute

/-! The activity, scalar flag, and chosen magic-corner bindings of the
 frozen pregame, before the common qutrit amplification. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestCoarse
open Compiler CompilerScaffold CompilerHonestFamilies CompilerHonestFMS
  CompilerHonestFMSWeights CompilerHonestCommute CompilerHonestDictionary
  CompilerHonestScalar CompilerFiniteRegister RowCompleteness

theorem bridgeActive_iff (g : Fin 4) (i : Fin 17) :
    bridgeActive g.val i=true ↔ ∃ a : Fin 5,i=position g a := by
  constructor
  · intro h
    simp only [bridgeActive,decide_eq_true_eq] at h
    rcases h with h | h
    · refine ⟨0,?_⟩
      have hg := g.isLt
      simpa [selected,position,show g.val<5 by omega] using h
    · refine ⟨⟨i.val-4*g.val,by have := i.isLt; omega⟩,?_⟩
      have ha : (⟨i.val-4*g.val,by have := i.isLt; omega⟩ : Fin 5)≠0 := by
        intro he
        have := congrArg Fin.val he
        simp only [Fin.val_zero] at this
        omega
      apply Fin.ext
      simp only [position,dif_neg ha]
      omega
  · rintro ⟨a,rfl⟩
    exact position_active g a

theorem embed_at {n d : ℕ} (e : Fin n → Fin d) (he : Function.Injective e)
    (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : embed e A (e a) (e b)=A a b := by
  simp [embed,Matrix.mul_apply,inclusion,he.eq_iff,eq_comm]

theorem active_diagonal (g : Fin 4) :
    active g=Matrix.diagonal (fun i => if bridgeActive g.val i then (1:ℂ) else 0) := by
  apply Matrix.ext
  intro i j
  by_cases hi : ∃ a : Fin 5,i=position g a
  · obtain ⟨a,rfl⟩ := hi
    by_cases hj : ∃ b : Fin 5,j=position g b
    · obtain ⟨b,rfl⟩ := hj
      rw [active,embed_at _ (position_injective g)]
      simp [Matrix.diagonal_apply,Matrix.one_apply,(position_injective g).eq_iff,position_active]
    · have hn : ∀ b,j≠position g b := by simpa using hj
      rw [active,embed_zero_outside _ _ _ _ (Or.inr hn)]
      have he : position g a≠j := by intro h; exact hn a h.symm
      simp [Matrix.diagonal_apply,he]
  · have hn : ∀ a,i≠position g a := by simpa using hi
    rw [active,embed_zero_outside _ _ _ _ (Or.inl hn)]
    have hb : bridgeActive g.val i≠true := by
      intro h
      exact hi ((bridgeActive_iff g i).mp h)
    simp [Matrix.diagonal_apply,hb]

theorem activity_sum (g : Fin 4) (Q : Partition (Matrix (Fin 5) (Fin 5) ℂ) (Fin 6))
    (hz : Q.effect 5=0) :
    (∑ a : Fin 6,if a.val<5 then
      (extend (position g) (position_injective g) Q hz).effect a else 0)=active g := by
  calc
    _=∑ a : Fin 6,embed (position g) (Q.effect a) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases he : a=5
      · subst a; simp [hz]
      · have hv : a.val<5 := by have := a.isLt; omega
        simp [extend,he,hv]
    _=embed (position g) (∑ a : Fin 6,Q.effect a) := (embed_sum _ _).symm
    _=active g := by rw [Q.total]; rfl

 def localCorner (a : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal (fun i => if i=a then 1 else 0)

theorem alice_flag (x : Fin 3) : CompilerHonestFMS.alice ⟨x.val,by have := x.isLt; omega⟩ 0=localCorner 0 := by
  apply Matrix.ext
  intro i j
  fin_cases x <;> fin_cases i <;> fin_cases j <;>
    norm_num [CompilerHonestFMS.alice,rankOne,aliceVector,aliceVector0,aliceVector1,aliceVector2,
      localCorner,Matrix.diagonal_apply]

theorem bob_flag (x : Fin 3) : CompilerHonestFMS.bob ⟨x.val,by have := x.isLt; omega⟩ 0=localCorner 0 := by
  apply Matrix.ext
  intro i j
  fin_cases x <;> fin_cases i <;> fin_cases j <;>
    norm_num [CompilerHonestFMS.bob,rankOne,bobVector,bobVector0,bobVector1,bobVector2,
      localCorner,Matrix.diagonal_apply]

theorem alice_magic (k : Fin 4) :
    CompilerHonestFMS.alice (if k=0 then 4 else 3)
      ⟨if k=0 then 2 else k.val+1,by have := k.isLt; split_ifs <;> omega⟩=
        localCorner ⟨k.val+1,by have := k.isLt; omega⟩ := by
  apply Matrix.ext
  intro i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [CompilerHonestFMS.alice,rankOne,aliceVector,aliceVector3,aliceVector4,
      localCorner,Matrix.diagonal_apply]

theorem bob_magic (k : Fin 4) :
    CompilerHonestFMS.bob 0 ⟨k.val+1,by have := k.isLt; omega⟩=
        localCorner ⟨k.val+1,by have := k.isLt; omega⟩ := by
  apply Matrix.ext
  intro i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [CompilerHonestFMS.bob,rankOne,bobVector,bobVector0,
      localCorner,Matrix.diagonal_apply]

 theorem embedded_corner (g : Fin 4) (a : Fin 5) :
    embed (position g) (localCorner a)=
      Matrix.diagonal (fun i => if i=position g a then (1:ℂ) else 0) := by
  apply Matrix.ext
  intro i j
  by_cases hi : ∃ b : Fin 5,i=position g b
  · obtain ⟨b,rfl⟩ := hi
    by_cases hj : ∃ c : Fin 5,j=position g c
    · obtain ⟨c,rfl⟩ := hj
      rw [embed_at _ (position_injective g)]
      simp [localCorner,Matrix.diagonal_apply,(position_injective g).eq_iff]
    · have hn : ∀ c,j≠position g c := by simpa using hj
      rw [embed_zero_outside _ _ _ _ (Or.inr hn)]
      have he : position g b≠j := by intro h; exact hn b h.symm
      simp [Matrix.diagonal_apply,he]
  · have hn : ∀ b,i≠position g b := by simpa using hi
    rw [embed_zero_outside _ _ _ _ (Or.inl hn)]
    by_cases he : i=j
    · subst j; simp [hn a]
    · simp [Matrix.diagonal_apply,he]


#print axioms active_diagonal
#print axioms activity_sum
#print axioms alice_flag
#print axioms bob_flag
#print axioms alice_magic
#print axioms bob_magic
end Sigma2.CompilerHonestCoarse
