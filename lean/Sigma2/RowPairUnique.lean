import Sigma2.RowGlobalUnique

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral FiniteJoint

def pairQ {s} (R : Rows s) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) : NewQ R :=
  ⟨.pair j,by
    have hmem : j ∈ (List.range (RowSlots.dimension R)).drop 1 := by
      rw [List.mem_iff_getElem]
      refine ⟨j-1,by simp; omega,?_⟩
      simp; omega
    have hm : (Question.pair j : Q R) ∈ ((List.range (RowSlots.dimension R)).drop 1).map (fun k => (Question.pair k : Q R)) :=
      List.mem_map.mpr ⟨j,hmem,rfl⟩
    simp only [questions,List.mem_append]
    tauto⟩

abbrev PairCheck {s} (R : Rows s) := Option (Fin (RowSlots.dimension R))

def pairSignature {s} (R : Rows s) (j : ℕ) : PairCheck R → ℕ → Bool
  | none,a => decide (a%2=1)
  | some ell,a => if parity (2*RowSlots.squares R) ell.val j then false
      else parity (2*RowSlots.squares R) ell.val (a/2)

def pairGlobal {s} (R : Rows s) : PairCheck R → NewQ R
  | none => globalQ R true
  | some _ => globalQ R false

def pairParity {s} (R : Rows s) (j : ℕ) : PairCheck R → ℕ → Bool
  | none,b => parity (2*RowSlots.squares R) j b
  | some ell,b => if parity (2*RowSlots.squares R) ell.val j then false
      else parity (2*RowSlots.squares R) ell.val b

def pairCheckList {s} (R : Rows s) : List (PairCheck R) :=
  none :: (List.finRange (RowSlots.dimension R)).map some

theorem pairCheck_mem {s} (R : Rows s) (k : PairCheck R) : k∈pairCheckList R := by
  cases k <;> simp [pairCheckList]

theorem pair_reject {s} (R : Rows s) (j : ℕ) (k : PairCheck R) (a b : ℕ)
    (hne : pairSignature R j k a≠pairParity R j k b) :
    newRule R (.pair j) (pairGlobal R k).val a b=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hd : directed R (.pair j) (pairGlobal R k).val a b=true := by
    simp only [newRule,Bool.and_eq_true] at hh
    exact hh.1.2
  cases k with
  | none =>
    have he : decide (a%2=1)=parity (2*RowSlots.squares R) j b := by
      simpa [pairGlobal,globalQ,directed] using hd
    exact hne he
  | some ell =>
    by_cases hp : parity (2*RowSlots.squares R) ell.val j=true
    · exact hne (by simp [pairSignature,pairParity,hp])
    · have hf : parity (2*RowSlots.squares R) ell.val j=false := Bool.eq_false_iff.mpr hp
      have hl : (List.range (RowSlots.dimension R)).all (fun l =>
          if parity (2*RowSlots.squares R) l j then true else
            decide (parity (2*RowSlots.squares R) l (a/2)=parity (2*RowSlots.squares R) l b))=true := by
        simpa [pairGlobal,globalQ,directed] using hd
      have he := (List.all_eq_true.mp hl) ell.val (List.mem_range.mpr ell.isLt)
      have heq : parity (2*RowSlots.squares R) ell.val (a/2)=parity (2*RowSlots.squares R) ell.val b := by
        simpa [hf] using he
      exact hne (by simpa [pairSignature,pairParity,hf] using heq)

/-- The actual table's sign and complete perpendicular syndrome distinguish
all valid canonical pair answers. -/
theorem pair_signature_injective {s} (R : Rows s) (j : ℕ) (hj : j<RowSlots.dimension R)
    (a b : ℕ) (ha : valid R (.pair j) a=true) (hb : valid R (.pair j) b=true)
    (he : ∀ k ∈ pairCheckList R,pairSignature R j k a=pairSignature R j k b) : a=b := by
  have hva : a<2*RowSlots.dimension R ∧ a/2≤Nat.xor (a/2) j := by simpa [valid] using ha
  have hvb : b<2*RowSlots.dimension R ∧ b/2≤Nat.xor (b/2) j := by simpa [valid] using hb
  have hrep : a/2=b/2 := by
    apply RowParity.canonical_unique (n:=2*RowSlots.squares R) (by simpa only [← dimension_bits] using hj)
      (by rw [← dimension_bits]; omega) (by rw [← dimension_bits]; omega) hva.2 hvb.2
    intro ell hell hperp
    have helld : ell<RowSlots.dimension R := by simpa only [dimension_bits] using hell
    have hh := he (some ⟨ell,helld⟩) (pairCheck_mem R _)
    simpa [pairSignature,hperp] using hh
  have hsign := he none (pairCheck_mem R _)
  have hs : (a%2=1 ↔ b%2=1) := by simpa [pairSignature] using hsign
  omega

/-- Complete pair-effect formula in the certified scalar algebra. Every factor
is a parity coarse event of the canonical global spectral family. -/
def pairJoint (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (j a : ℕ) : Op :=
  if valid R (.pair j) a then
    intersection P (fun k =>
      coarse (fun b : Answer G R => globalJoint bob G R M P (k.isNone) b.val)
        (fun b => pairParity R j k b.val) (pairSignature R j k a)) (pairCheckList R)
  else 0

/-- Both parties' actual complete scalar-pair measurements are identified,
with the parity checks and canonical representatives of the actual table. -/
theorem pair_unique (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (a : Answer G R) :
    newEffects bob G R S.measurements P (pairQ R j hj) a=
      pairJoint bob G R S.measurements P j a.val := by
  let B := newEffects bob G R S.measurements P (pairQ R j hj)
  have hc (k : PairCheck R) (t : Bool) :=
    new_coarse_eq bob G R S hS h hm P hP (pairQ R j hj) (pairGlobal R k)
      (pairSignature R j k) (pairParity R j k) (pair_reject R j k) t
  by_cases ha : valid R (.pair j) a.val=true
  · rw [pairJoint,if_pos ha]
    have he := fine_unique B P hP.1
      (new_positive bob G R S.measurements P hP.1 _) (new_sum bob G R S.measurements P hP.1 _)
      (fun b => valid R (.pair j) b.val=true)
      (fun b hb => new_invalid_zero bob G R S hS h hm P hP _ b (by
        simpa only [pairQ] using Bool.eq_false_iff.mpr hb))
      (fun (k : PairCheck R) (a : Answer G R) => pairSignature R j k a.val) (pairCheckList R) a
      (fun k => (hc k (pairSignature R j k a.val)).2) ha (by
        intro b hb heq
        apply Fin.ext
        exact pair_signature_injective R j hj.2 b.val a.val hb ha heq)
    change B a=_
    rw [he]
    apply congrArg (fun C : PairCheck R → Op => intersection P C (pairCheckList R))
    funext k
    rw [(hc k (pairSignature R j k a.val)).1]
    apply congrArg (fun E : Answer G R → Op => coarse E (fun b => pairParity R j k b.val) (pairSignature R j k a.val))
    funext b
    cases k with
    | none => exact global_unique bob G R S hS h hm P hP true b
    | some ell => exact global_unique bob G R S hS h hm P hP false b
  · have hf : valid R (.pair j) a.val=false := Bool.eq_false_iff.mpr ha
    rw [pairJoint,if_neg ha]
    exact new_invalid_zero bob G R S hS h hm P hP _ a (by simpa only [pairQ] using hf)

#print axioms pairCheck_mem
#print axioms pair_reject
#print axioms pair_signature_injective
#print axioms pair_unique
end Sigma2.RowScalar



