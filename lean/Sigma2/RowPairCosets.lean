import Sigma2.RowPairUnique

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
set_option maxRecDepth 2000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral FiniteJoint

theorem parity_right_xor (n ell a b : ℕ) :
    parity n ell (Nat.xor a b)=Bool.xor (parity n ell a) (parity n ell b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [RowParity.parity_succ,RowParity.parity_succ,RowParity.parity_succ,ih,Nat.xor_eq,Nat.testBit_xor]
    cases h1 : parity n ell a <;> cases h2 : parity n ell b <;>
      cases h3 : Nat.testBit ell n <;> cases h4 : Nat.testBit a n <;> cases h5 : Nat.testBit b n <;> decide

theorem syndrome_iff_coset {s} (R : Rows s) {j r b : ℕ}
    (hj : j<RowSlots.dimension R) (hr : r<RowSlots.dimension R) (hb : b<RowSlots.dimension R) :
    (∀ ell,ell<RowSlots.dimension R → parity (2*RowSlots.squares R) ell j=false →
      parity (2*RowSlots.squares R) ell b=parity (2*RowSlots.squares R) ell r) ↔
      b=r ∨ b=Nat.xor r j := by
  constructor
  · intro he
    apply RowParity.coset_separation (n:=2*RowSlots.squares R)
      (by simpa [← dimension_bits] using hj) (by simpa [← dimension_bits] using hb)
      (by simpa [← dimension_bits] using hr)
    intro ell hell hperp
    exact he ell (by simpa only [dimension_bits] using hell) hperp
  · rintro (rfl | rfl) ell hell hperp
    · rfl
    · rw [parity_right_xor,hperp]; simp

theorem intersection_map {κ τ : Type} (P : Op) (C : τ → Op) (f : κ → τ) (ks : List κ) :
    intersection P C (ks.map f)=intersection P (fun k => C (f k)) ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [List.map_cons,intersection,ih]

/-- The complete perpendicular-syndrome intersection is exactly the two-point
Z coset. This includes all cosets, rather than only the zero syndrome. -/
theorem pair_syndrome_coset (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (r : ℕ) (hr : r<RowSlots.dimension R) :
    let Z := newEffects bob G R S.measurements P (globalQ R false)
    intersection P (fun ell : Fin (RowSlots.dimension R) =>
      coarse Z (fun b => pairParity R j (some ell) b.val)
        (if parity (2*RowSlots.squares R) ell.val j then false
          else parity (2*RowSlots.squares R) ell.val r)) (List.finRange (RowSlots.dimension R))=
      coarse Z (fun b => decide (b.val=r ∨ b.val=Nat.xor r j)) true := by
  dsimp only
  let Z := newEffects bob G R S.measurements P (globalQ R false)
  let f := fun ell : Fin (RowSlots.dimension R) => fun b : Answer G R => pairParity R j (some ell) b.val
  let v := fun ell : Fin (RowSlots.dimension R) =>
    if parity (2*RowSlots.squares R) ell.val j then false else parity (2*RowSlots.squares R) ell.val r
  have hp (ell : Fin (RowSlots.dimension R)) : Projection (coarse Z (f ell) (v ell)) := by
    have hh := new_coarse_eq bob G R S hS h hm P hP (pairQ R j hj) (pairGlobal R (some ell))
      (pairSignature R j (some ell)) (pairParity R j (some ell)) (pair_reject R j (some ell)) (v ell)
    rw [hh.1] at hh
    exact hh.2
  let D := intersection P (fun ell => coarse Z (f ell) (v ell)) (List.finRange (RowSlots.dimension R))
  have hsum : D=∑ b,D*Z b := by
    rw [← Finset.mul_sum,new_sum bob G R S.measurements P hP.1 (globalQ R false)]
    exact (intersection_supported P hP.1.2 _ _).symm
  change D=_
  rw [hsum]
  unfold coarse
  apply Finset.sum_congr rfl
  intro b _
  change D*Z b=if decide (b.val=r ∨ b.val=Nat.xor r j)=true then Z b else 0
  rw [intersection_action Z P hP.1 (new_positive bob G R S.measurements P hP.1 _)
    (new_sum bob G R S.measurements P hP.1 _) f v hp]
  by_cases hb : b.val<RowSlots.dimension R
  · have he : (∀ ell ∈ List.finRange (RowSlots.dimension R),f ell b=v ell) ↔
        b.val=r ∨ b.val=Nat.xor r j := by
      rw [← syndrome_iff_coset R hj.2 hr hb]
      constructor
      · intro hh ell hell hperp
        have he := hh ⟨ell,hell⟩ (List.mem_finRange _)
        simpa [f,v,pairParity,hperp] using he
      · intro hh ell hell
        by_cases hperp : parity (2*RowSlots.squares R) ell.val j=true
        · simp [f,v,pairParity,hperp]
        · have hf := Bool.eq_false_iff.mpr hperp
          simpa [f,v,pairParity,hf] using hh ell.val ell.isLt hf
    simp only [he,decide_eq_true_eq]
  · have hz : Z b=0 := new_invalid_zero bob G R S hS h hm P hP _ b (by simp [globalQ,valid,hb])
    simp [hz]


/-- Each actual pair effect is the product of its X-parity sign projection
and exactly its two-point Z-coset projection. This is the full pair formula,
including every nonzero syndrome and the canonical zero-syndrome events. -/
theorem pair_coset_formula (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (a : Answer G R)
    (ha : valid R (.pair j) a.val=true) :
    newEffects bob G R S.measurements P (pairQ R j hj) a=
      coarse (newEffects bob G R S.measurements P (globalQ R true))
        (fun b => parity (2*RowSlots.squares R) j b.val) (decide (a.val%2=1)) *
      coarse (newEffects bob G R S.measurements P (globalQ R false))
        (fun b => decide (b.val=a.val/2 ∨ b.val=Nat.xor (a.val/2) j)) true := by
  rw [pair_unique bob G R S hS h hm P hP,pairJoint,if_pos ha]
  have he : (fun k : PairCheck R =>
      coarse (fun b : Answer G R => globalJoint bob G R S.measurements P k.isNone b.val)
        (fun b => pairParity R j k b.val) (pairSignature R j k a.val))=
      (fun k => coarse (newEffects bob G R S.measurements P (pairGlobal R k))
        (fun b => pairParity R j k b.val) (pairSignature R j k a.val)) := by
    funext k
    apply congrArg (fun B : Answer G R → Op => coarse B (fun b => pairParity R j k b.val) (pairSignature R j k a.val))
    funext b
    cases k with
    | none => exact (global_unique bob G R S hS h hm P hP true b).symm
    | some ell => exact (global_unique bob G R S hS h hm P hP false b).symm
  rw [he,pairCheckList,intersection,intersection_map]
  change coarse (newEffects bob G R S.measurements P (globalQ R true))
      (fun b => parity (2*RowSlots.squares R) j b.val) (decide (a.val%2=1)) *
      intersection P (fun ell : Fin (RowSlots.dimension R) =>
        coarse (newEffects bob G R S.measurements P (globalQ R false))
          (fun b => pairParity R j (some ell) b.val)
          (if parity (2*RowSlots.squares R) ell.val j then false
            else parity (2*RowSlots.squares R) ell.val (a.val/2))) (List.finRange _) = _
  rw [pair_syndrome_coset bob G R S hS h hm P hP j hj (a.val/2) (by
    have hv : a.val<2*RowSlots.dimension R ∧ a.val/2≤Nat.xor (a.val/2) j := by simpa [valid] using ha
    omega)]


#print axioms parity_right_xor
#print axioms syndrome_iff_coset
#print axioms intersection_map
#print axioms pair_syndrome_coset
#print axioms pair_coset_formula
end Sigma2.RowScalar

