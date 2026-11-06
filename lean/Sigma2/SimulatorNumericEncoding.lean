import Sigma2.SimulatorNumericTracks

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Sigma2.SimulatorNumericEncoding
open Turing Sigma2.Tree Sigma2.SimulatorNumbered Sigma2.SimulatorParameter Sigma2.SimulatorParameterCoding
  Sigma2.SimulatorParameterKernel Sigma2.SimulatorNumericLocal Sigma2.SimulatorNumericTracks

local instance : Nonempty SimulatorLoader.Control := ⟨.origin⟩
variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q] [Fintype Γ] [Fintype Q]
  [DecidableEq Γ] [DecidableEq Q]
local instance (e : ℕ) : DecidableEq (SimulatorLoader.State Γ (Label e Q)) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

def headPack (q : Option ℕ) : ℕ := (q.map (fun n => n+1)).getD 0
def headUnpack (k : ℕ) : Option ℕ := if k=0 then none else some (k-1)
def headSize (e : ℕ) : ℕ := (labelCoding (Coding.fixed Q) e).size+1
def cellSize (e : ℕ) : ℕ := (Coding.fixed Γ).size * headSize (Q:=Q) e

def cellPack (e : ℕ) (c : CellRep Γ) : ℕ :=
  (Coding.fixed Γ).enc c.1 * headSize (Q:=Q) e + headPack c.2
def cellUnpack (e : ℕ) (k : ℕ) : CellRep Γ :=
  ((Coding.fixed Γ).dec (k/headSize (Q:=Q) e),headUnpack (k%headSize (Q:=Q) e))

def pack (e : ℕ) (s : StateRep Γ) : ℕ :=
  ((Coding.fixed SimulatorLoader.Control).option.enc s.1) *
      ((Coding.fixed (Fin 5)).size * (cellSize (Γ:=Γ) (Q:=Q) e * cellSize (Γ:=Γ) (Q:=Q) e)) +
    ((Coding.fixed (Fin 5)).enc s.2.1 * (cellSize (Γ:=Γ) (Q:=Q) e * cellSize (Γ:=Γ) (Q:=Q) e) +
      (cellPack (Q:=Q) e s.2.2.1 * cellSize (Γ:=Γ) (Q:=Q) e + cellPack (Q:=Q) e s.2.2.2))

def unpack (e k : ℕ) : StateRep Γ :=
  let d := cellSize (Γ:=Γ) (Q:=Q) e
  let p := d*d
  let t := (Coding.fixed (Fin 5)).size*p
  let v := k%t
  let w := v%p
  ((Coding.fixed SimulatorLoader.Control).option.dec (k/t),
    ((Coding.fixed (Fin 5)).dec (v/p),
      (cellUnpack (Γ:=Γ) (Q:=Q) e (w/d),cellUnpack (Γ:=Γ) (Q:=Q) e (w%d))))

lemma pack_rep (e : ℕ) (s : SimulatorLoader.State Γ (Label e Q)) :
    pack (Q:=Q) e (stateRep e s)=(stateCoding (Coding.fixed Γ) (Coding.fixed Q) e).enc s := by
  rcases s with ⟨ctl,f,⟨u,hu⟩,⟨v,hv⟩⟩
  cases hu <;> cases hv <;>
    rfl

lemma dec_unpack (e k : ℕ) : stateDec (Q:=Q) e (unpack (Γ:=Γ) (Q:=Q) e k)=
    (stateCoding (Coding.fixed Γ) (Coding.fixed Q) e).dec k := by
  unfold stateDec unpack cellUnpack cellDec headUnpack stateCoding Coding.prod Coding.option
  dsimp only [cellSize,headSize]
  split_ifs <;> simp_all

def startRep (z : Γ) : StateRep Γ :=
  (some .origin,(0,((z,none),(default,none))))
def blankRep : StateRep Γ :=
  (none,(1,((default,none),(default,none))))
def rejectRep : StateRep Γ :=
  (none,(2,((default,none),(default,none))))

def encodeNum (z : Γ) (e : ℕ) (s : StateRep Γ) : ℕ :=
  if s=startRep z then 0 else if s=blankRep then 1 else if s=rejectRep then 2 else pack (Q:=Q) e s+3

def decodeNum (z : Γ) (e k : ℕ) : StateRep Γ :=
  if k=0 then startRep z else if k=1 then blankRep else if k=2 then rejectRep else unpack (Q:=Q) e (k-3)

variable (M : TM0.Machine Γ Q) (a z sep : Γ)

lemma encode_eq (e : ℕ) (s : SimulatorLoader.State Γ (Label e Q)) :
    (SimulatorNumbered.encode (SimulatorLoader.rule (machine M a z sep e) a z)
      (stateCoding (Coding.fixed Γ) (Coding.fixed Q) e) s).val=
      encodeNum (Q:=Q) z e (stateRep e s) := by
  have hs : stateRep e (SimulatorLoader.rule (machine M a z sep e) a z).start=startRep z := rfl
  have hb : stateRep e (SimulatorLoader.rule (machine M a z sep e) a z).blank=blankRep := rfl
  have hr : stateRep e (SimulatorLoader.rule (machine M a z sep e) a z).reject=rejectRep := rfl
  have hstart : stateRep e s=startRep z ↔ s=(SimulatorLoader.rule (machine M a z sep e) a z).start :=
    by rw [← hs]; exact (stateRep_injective (Γ:=Γ) (Q:=Q) e).eq_iff
  have hblank : stateRep e s=blankRep ↔ s=(SimulatorLoader.rule (machine M a z sep e) a z).blank :=
    by rw [← hb]; exact (stateRep_injective (Γ:=Γ) (Q:=Q) e).eq_iff
  have hreject : stateRep e s=rejectRep ↔ s=(SimulatorLoader.rule (machine M a z sep e) a z).reject :=
    by rw [← hr]; exact (stateRep_injective (Γ:=Γ) (Q:=Q) e).eq_iff
  unfold SimulatorNumbered.encode encodeNum
  simp only [hstart,hblank,hreject]
  split_ifs <;> simp_all [pack_rep]

lemma decode_eq (e : ℕ) (k : Fin ((stateCoding (Coding.fixed Γ) (Coding.fixed Q) e).size+3)) :
    stateDec (Q:=Q) e (decodeNum (Q:=Q) z e k.val)=
      SimulatorNumbered.decode (SimulatorLoader.rule (machine M a z sep e) a z)
        (stateCoding (Coding.fixed Γ) (Coding.fixed Q) e) k := by
  unfold decodeNum SimulatorNumbered.decode
  split_ifs <;> first | rfl | exact dec_unpack e (k.val-3)

def entryNum (e k : ℕ) : ℕ :=
  let n := (stateCoding (Coding.fixed Γ) (Coding.fixed Q) e).size+3
  let q := k/2/n/n
  let l : Option ℕ := if q=0 then none else some ((q-1)%n)
  let c := (k/2/n)%n
  let r := (k/2)%n
  if l=some 1 ∧ c=1 ∧ r=1 then 1 else
    encodeNum (Q:=Q) z e (updateNum M a z sep e
      (l.map (decodeNum (Q:=Q) z e)) (decodeNum (Q:=Q) z e c) (decodeNum (Q:=Q) z e r)
      (decide (k%2=1)))

lemma update_value (e : ℕ)
    (l : Option (Fin ((stateCoding (Coding.fixed Γ) (Coding.fixed Q) e).size+3)))
    (c r : Fin ((stateCoding (Coding.fixed Γ) (Coding.fixed Q) e).size+3)) (b : Bool) :
    ((family M a z sep (Coding.fixed Γ) (Coding.fixed Q) e).update l c r b).val=
      if l.map Fin.val=some 1 ∧ c.val=1 ∧ r.val=1 then 1 else
        encodeNum (Q:=Q) z e (updateNum M a z sep e
          (l.map (fun k => decodeNum (Q:=Q) z e k.val))
          (decodeNum (Q:=Q) z e c.val) (decodeNum (Q:=Q) z e r.val) b) := by
  have h1 : (1 : Fin ((stateCoding (Coding.fixed Γ) (Coding.fixed Q) e).size+3)).val=1 := by
    change 1%_=1
    apply Nat.mod_eq_of_lt
    omega
  have hl : l=some 1 ↔ l.map Fin.val=some 1 := by
    cases l <;> simp [Fin.ext_iff, h1]
  have hc : c=1 ↔ c.val=1 := by simp [Fin.ext_iff,h1]
  have hr : r=1 ↔ r.val=1 := by simp [Fin.ext_iff,h1]
  unfold family SimulatorNumbered.automaton
  simp only [hl,hc,hr]
  split_ifs
  · rfl
  · rw [encode_eq]
    have hd : SimulatorNumbered.decode (SimulatorLoader.rule (machine M a z sep e) a z)
          (stateCoding (Coding.fixed Γ) (Coding.fixed Q) e) =
        fun k => stateDec (Q:=Q) e (decodeNum (Q:=Q) z e k.val) :=
      funext (fun k => (decode_eq M a z sep e k).symm)
    rw [hd]
    simpa only [Option.map_map,Function.comp_def,SimulatorLoader.rule] using
      congrArg (encodeNum (Q:=Q) z e) (update_eq M a z sep e
        (l.map (fun k => decodeNum (Q:=Q) z e k.val))
        (decodeNum (Q:=Q) z e c.val) (decodeNum (Q:=Q) z e r.val) b)

lemma entry_eq (e k : ℕ) :
    SimulatorEncoding.localEntry (family M a z sep (Coding.fixed Γ) (Coding.fixed Q) e) k=
      entryNum M a z sep e k := by
  unfold SimulatorEncoding.localEntry
  rw [update_value]
  unfold entryNum
  dsimp only [family,SimulatorNumbered.automaton]
  by_cases h : k/2/((stateCoding (Coding.fixed Γ) (Coding.fixed Q) e).size+3)/
      ((stateCoding (Coding.fixed Γ) (Coding.fixed Q) e).size+3)=0
  all_goals simp only [h,ite_true,ite_false,Option.map_none,Option.map_some]
  all_goals rfl


#print axioms entry_eq
end Sigma2.SimulatorNumericEncoding

