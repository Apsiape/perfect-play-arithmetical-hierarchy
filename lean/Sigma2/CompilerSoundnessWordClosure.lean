import Sigma2.CompilerSoundnessJoints

/-! Closure facts for the exact finite retained-word dictionary. -/
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical
namespace Sigma2.CompilerSoundnessWordClosure
open CompilerScaffold
attribute [local irreducible] CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials

theorem closure_empty (w : Word) : [] ∈ wordClosure w := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨0,List.mem_range.mpr (by omega),by simp⟩

theorem closure_take (w u : Word) (hu : u ∈ wordClosure w) (n : ℕ) :
    u.take n ∈ wordClosure w := by
  rcases List.mem_append.mp hu with hpre|hatom
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hpre
    apply List.mem_append_left
    rw [List.take_take]
    exact List.mem_map.mpr ⟨min n k,List.mem_range.mpr (by
      have := List.mem_range.mp hk
      have := Nat.min_le_right n k
      omega),rfl⟩
  · obtain ⟨t,ht,hu'⟩ := List.mem_flatMap.mp hatom
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu'
    rcases hu' with rfl|rfl <;> cases n with
    | zero => exact closure_empty w
    | succ n => simpa using hu

theorem closure_atoms (w : Word) (t : Token) (ht : t ∈ w) :
    [t] ∈ wordClosure w ∧ [(t.1,!t.2)] ∈ wordClosure w := by
  constructor
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨t,ht,by simp⟩
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨t,ht,by simp⟩

theorem closure_singletons (w u : Word) (hu : u ∈ wordClosure w)
    (t : Token) (ht : t ∈ u) :
    [t] ∈ wordClosure w ∧ [(t.1,!t.2)] ∈ wordClosure w := by
  rcases List.mem_append.mp hu with hpre|hatom
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hpre
    exact closure_atoms w t (List.mem_of_mem_take ht)
  · obtain ⟨s,hs,hu'⟩ := List.mem_flatMap.mp hatom
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu'
    rcases hu' with rfl|rfl
    · have he : t=s := by simpa using ht
      subst t
      exact closure_atoms w s hs
    · have he : t=(s.1,!s.2) := by simpa using ht
      subst t
      have hh := closure_atoms w s hs
      exact ⟨hh.2,by simpa only [Bool.not_not] using hh.1⟩

theorem words_take (P : Presentation) (w : Word) (hw : w ∈ words P) (n : ℕ) :
    w.take n ∈ words P := by
  simp only [words,List.mem_dedup] at hw ⊢
  rcases List.mem_cons.mp hw with rfl|hw
  · simp only [List.take_nil]
    exact List.mem_cons_self ..
  · obtain ⟨p,hp,hp'⟩ := List.mem_flatMap.mp hw
    obtain ⟨t,ht,ht'⟩ := List.mem_flatMap.mp hp'
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨p,hp,List.mem_flatMap.mpr ⟨t,ht,closure_take t.2 w ht' n⟩⟩

theorem words_singletons (P : Presentation) (w : Word) (hw : w ∈ words P)
    (t : Token) (ht : t ∈ w) : [t] ∈ words P ∧ [(t.1,!t.2)] ∈ words P := by
  simp only [words,List.mem_dedup] at hw ⊢
  rcases List.mem_cons.mp hw with rfl|hw
  · simp at ht
  · obtain ⟨p,hp,hp'⟩ := List.mem_flatMap.mp hw
    obtain ⟨s,hs,hs'⟩ := List.mem_flatMap.mp hp'
    have hh := closure_singletons s.2 w hs' t ht
    constructor
    · apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨p,hp,List.mem_flatMap.mpr ⟨s,hs,hh.1⟩⟩
    · apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨p,hp,List.mem_flatMap.mpr ⟨s,hs,hh.2⟩⟩

end Sigma2.CompilerSoundnessWordClosure
