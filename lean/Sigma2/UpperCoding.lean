import Sigma2.Statements
import Mathlib.Computability.RE

namespace Sigma2.UpperCoding

def rationalCode (n : ℕ) : ℚ := (Encodable.decode (α := ℚ) n).getD 0

open Encodable Primrec

theorem int_encode_nat (n : ℕ) : encode (n : ℤ) = 2*n := by
  change Equiv.intEquivNat _ = _
  rfl
theorem int_encode_neg (n : ℕ) : encode (Int.negSucc n) = 2*n+1 := by
  change Equiv.intEquivNat _ = _
  rfl
theorem int_natAbs : Primrec Int.natAbs := by
  refine (nat_div.comp (succ.comp (@Primrec.encode ℤ _)) (const 2)).of_eq ?_
  intro z
  cases z with
  | ofNat n => change (2*n+1)/2 = n; omega
  | negSucc n => change (2*n+1+1)/2 = n+1; omega

theorem nat_gcd : Primrec₂ Nat.gcd := by
  have hp : PrimrecRel (fun p : ℕ × ℕ => fun k : ℕ => p.1 % k = 0 ∧ p.2 % k = 0) :=
    (Primrec.eq.comp (nat_mod.comp (fst.comp fst) snd) (const 0)).and
      (Primrec.eq.comp (nat_mod.comp (snd.comp fst) snd) (const 0))
  refine (Primrec.ite (Primrec.eq.comp snd (const 0)) fst
    (nat_findGreatest snd hp)).to₂.of_eq ?_
  intro a b
  by_cases hb : b = 0
  · simp [hb]
  · simp only [hb, ↓reduceIte]
    apply le_antisymm
    · have hs := Nat.findGreatest_spec (P := fun k => a % k = 0 ∧ b % k = 0)
        (Nat.gcd_le_right a (Nat.pos_of_ne_zero hb))
        (show a % a.gcd b = 0 ∧ b % a.gcd b = 0 from
          ⟨Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b),
           Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b)⟩)
      exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_right a (Nat.pos_of_ne_zero hb))
        (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hs.1) (Nat.dvd_of_mod_eq_zero hs.2))
    · exact Nat.le_findGreatest (P := fun k => a % k = 0 ∧ b % k = 0)
        (Nat.gcd_le_right a (Nat.pos_of_ne_zero hb))
        ⟨Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b),
          Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b)⟩

theorem rat_valid : PrimrecPred (fun p : ℤ × ℕ => 0 < p.2 ∧ p.1.natAbs.Coprime p.2) :=
  (nat_lt.comp (const 0) snd).and
    ((Primrec.eq.comp (nat_gcd.comp (int_natAbs.comp fst) snd) (const 1)).of_eq
      (fun _ => Iff.rfl))

def ratEquiv : ℚ ≃ {p : ℤ × ℕ // 0 < p.2 ∧ p.1.natAbs.Coprime p.2} where
  toFun q := ⟨(q.num,q.den),q.pos,q.reduced⟩
  invFun p := ⟨p.1.1,p.1.2,ne_of_gt p.2.1,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible]
def ratPrimcodable : Primcodable ℚ := by
  letI := Primcodable.subtype rat_valid
  let alt := Primcodable.ofEquiv _ ratEquiv
  refine { toEncodable := Rat.instEncodable, prim := ?_ }
  have h := @Primcodable.prim ℚ alt
  convert h using 1
  funext n
  simp [this, Encodable.encode, Encodable.decode, alt, Rat.instEncodable,
    Primcodable.ofEquiv, ratEquiv, Encodable.ofEquiv, Encodable.decodeSigma,
    Encodable.decodeSubtype, Encodable.encodeSigma, Encodable.encodeSubtype,
    Primcodable.subtype, Encodable.Prod.encodable, Function.comp_def]
  split <;> rfl

instance : Primcodable ℚ where
  toEncodable := Rat.instEncodable
  prim := ratPrimcodable.prim

theorem rational_decode : Primrec rationalCode :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const 0)

theorem rat_num : Primrec Rat.num := by
  apply Primrec.encode_iff.mp
  exact ((Primrec.fst.comp (Primrec.unpair.comp (@Primrec.encode ℚ _)))).of_eq (fun q => by change (Nat.unpair (Nat.pair (encode q.num) q.den)).1 = _; simp)

theorem rat_den : Primrec Rat.den := by
  exact ((Primrec.snd.comp (Primrec.unpair.comp (@Primrec.encode ℚ _)))).of_eq (fun q => by change (Nat.unpair (Nat.pair (encode q.num) q.den)).2 = _; simp)

theorem int_ofNat : Primrec (fun n : ℕ => (n : ℤ)) :=
  Primrec.encode_iff.mp (nat_mul.comp (const 2) Primrec.id)

theorem int_negSucc : Primrec Int.negSucc :=
  Primrec.encode_iff.mp (succ.comp (nat_mul.comp (const 2) Primrec.id))

theorem int_subNatNat : Primrec₂ Int.subNatNat := by
  refine (Primrec.ite (nat_le.comp snd fst)
    (int_ofNat.comp (nat_sub.comp fst snd))
    (int_negSucc.comp (nat_sub.comp (nat_sub.comp snd fst) (const 1)))).to₂.of_eq ?_
  intro m n
  split <;> simp only [Int.subNatNat_eq_coe] <;> omega

theorem int_toNat : Primrec Int.toNat := by
  refine (Primrec.ite (Primrec.eq.comp (nat_mod.comp Primrec.encode (const 2)) (const 0))
    (nat_div.comp Primrec.encode (const 2)) (const 0)).of_eq ?_
  intro z
  cases z with
  | ofNat n => change (if (2*n)%2 = 0 then (2*n)/2 else 0) = n; split <;> omega
  | negSucc n => change (if (2*n+1)%2 = 0 then (2*n+1)/2 else 0) = 0; split <;> omega

theorem int_neg : Primrec (fun z : ℤ => -z) := by
  refine (Primrec.ite (Primrec.eq.comp (nat_mod.comp Primrec.encode (const 2)) (const 0))
    (int_subNatNat.comp (const 0) (nat_div.comp Primrec.encode (const 2)))
    (int_ofNat.comp (succ.comp (nat_div.comp Primrec.encode (const 2))))).of_eq ?_
  intro z
  cases z with
  | ofNat n =>
    change (if (2*n)%2 = 0 then Int.subNatNat 0 ((2*n)/2) else ↑((2*n)/2+1)) = -(n:ℤ)
    rw [ite_eq_left (by omega), Int.subNatNat_eq_coe]
    omega
  | negSucc n =>
    change (if (2*n+1)%2 = 0 then Int.subNatNat 0 ((2*n+1)/2) else ↑((2*n+1)/2+1)) = _
    have h : (2*n+1)%2 ≠ 0 := by omega
    rw [ite_eq_right h]
    congr 1 <;> omega

theorem int_decomp (z : ℤ) : (z.toNat : ℤ) - (-z).toNat = z := by omega

theorem int_add : Primrec₂ (fun a b : ℤ => a+b) := by
  refine (int_subNatNat.comp
    (nat_add.comp (int_toNat.comp fst) (int_toNat.comp snd))
    (nat_add.comp (int_toNat.comp (int_neg.comp fst))
      (int_toNat.comp (int_neg.comp snd)))).to₂.of_eq ?_
  intro a b
  simp only [Int.subNatNat_eq_coe, Nat.cast_add]
  have := int_decomp a
  have := int_decomp b
  omega

theorem int_mul : Primrec₂ (fun a b : ℤ => a*b) := by
  let ap := int_toNat.comp (Primrec.fst : Primrec (fun p : ℤ × ℤ => p.1))
  let bp := int_toNat.comp (Primrec.snd : Primrec (fun p : ℤ × ℤ => p.2))
  let an := int_toNat.comp (int_neg.comp (Primrec.fst : Primrec (fun p : ℤ × ℤ => p.1)))
  let bn := int_toNat.comp (int_neg.comp (Primrec.snd : Primrec (fun p : ℤ × ℤ => p.2)))
  refine (int_subNatNat.comp
    (nat_add.comp (nat_mul.comp ap bp) (nat_mul.comp an bn))
    (nat_add.comp (nat_mul.comp ap bn) (nat_mul.comp an bp))).to₂.of_eq ?_
  intro a b
  simp only [Int.subNatNat_eq_coe, Nat.cast_add, Nat.cast_mul]
  have ha := int_decomp a
  have hb := int_decomp b
  calc
    _ = ((a.toNat : ℤ) - (-a).toNat) * ((b.toNat : ℤ) - (-b).toNat) := by ring
    _ = a*b := by rw [ha,hb]

theorem int_lt : PrimrecRel (fun a b : ℤ => a<b) := by
  refine (nat_lt.comp
    (nat_add.comp (int_toNat.comp fst) (int_toNat.comp (int_neg.comp snd)))
    (nat_add.comp (int_toNat.comp snd) (int_toNat.comp (int_neg.comp fst)))).of_eq ?_
  intro p
  have := int_decomp p.1
  have := int_decomp p.2
  omega

theorem rat_lt : PrimrecRel (fun a b : ℚ => a<b) := by
  exact (int_lt.comp
    (int_mul.comp (rat_num.comp fst) (int_ofNat.comp (rat_den.comp snd)))
    (int_mul.comp (rat_num.comp snd) (int_ofNat.comp (rat_den.comp fst)))).of_eq
      (fun p => (Rat.lt_iff p.1 p.2).symm)


@[simp] theorem rational_encode (q : ℚ) : rationalCode (encode q) = q := by
  simp [rationalCode]

theorem rat_cross (q : ℚ) (z : ℤ) (n : ℕ) (hn : n ≠ 0) :
    q.num * (n : ℤ) = z * q.den ↔ q = (z : ℚ)/n := by
  have hdn : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hnn : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  constructor
  · intro h
    calc
      q = (q.num:ℚ)/q.den := (Rat.num_div_den q).symm
      _ = (z:ℚ)/n := (div_eq_div_iff hdn hnn).mpr (by exact_mod_cast h)
  · intro h
    have h' := (div_eq_div_iff hdn hnn).mp ((Rat.num_div_den q).trans h)
    exact_mod_cast h' 

theorem rat_fraction : Computable (fun p : ℤ × ℕ => (p.1 : ℚ)/(p.2+1)) := by
  let P : (ℤ × ℕ) → ℕ → Prop := fun p c =>
    (rationalCode c).num * ((p.2+1 : ℕ) : ℤ) = p.1 * (rationalCode c).den
  have hp : ComputablePred (fun p : (ℤ × ℕ) × ℕ => P p.1 p.2) := by
    apply PrimrecPred.computablePred
    exact Primrec.eq.comp
      (int_mul.comp (rat_num.comp (rational_decode.comp snd))
        (int_ofNat.comp (succ.comp (snd.comp fst))))
      (int_mul.comp (fst.comp fst) (int_ofNat.comp (rat_den.comp (rational_decode.comp snd))))
  have hx : ∀ p, ∃ c, P p c := by
    intro p
    refine ⟨encode ((p.1 : ℚ)/(p.2+1)), ?_⟩
    dsimp [P]
    rw [rational_encode]
    apply (rat_cross _ _ _ (Nat.succ_ne_zero _)).mpr
    push_cast
    rfl
  refine ((rational_decode.to_comp).comp (Computable.find hp hx)).of_eq ?_
  intro p
  have h := (rat_cross _ _ _ (Nat.succ_ne_zero p.2)).mp (Nat.find_spec (hx p))
  simpa only [Nat.cast_succ] using h

theorem rat_divNat : Computable (fun p : ℤ × ℕ => (p.1 : ℚ)/p.2) := by
  refine ((Primrec.eq.comp snd (const 0)).computablePred.decide.cond
    (Computable.const 0)
    (rat_fraction.comp (Computable.fst.pair (Computable.pred.comp Computable.snd)))).of_eq ?_
  intro p
  by_cases h : p.2 = 0
  · simp [h]
  · have hc : (↑(p.2-1):ℚ)+1 = (p.2:ℚ) := by
      exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h)
    simp [h,hc]

theorem rat_add : Computable₂ (fun a b : ℚ => a+b) := by
  refine (rat_divNat.comp
    ((int_add.comp
      (int_mul.comp (rat_num.comp fst) (int_ofNat.comp (rat_den.comp snd)))
      (int_mul.comp (rat_num.comp snd) (int_ofNat.comp (rat_den.comp fst)))).pair
      (nat_mul.comp (rat_den.comp fst) (rat_den.comp snd))).to_comp).to₂.of_eq ?_
  rintro ⟨a,b⟩
  dsimp
  push_cast
  have ha : (a.den:ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  have hb : (b.den:ℚ) ≠ 0 := by exact_mod_cast b.den_nz
  calc
    _ = (a.num:ℚ)/a.den + (b.num:ℚ)/b.den := by field_simp
    _ = a+b := by rw [Rat.num_div_den, Rat.num_div_den]

theorem rat_mul : Computable₂ (fun a b : ℚ => a*b) := by
  refine (rat_divNat.comp
    ((int_mul.comp (rat_num.comp fst) (rat_num.comp snd)).pair
      (nat_mul.comp (rat_den.comp fst) (rat_den.comp snd))).to_comp).to₂.of_eq ?_
  rintro ⟨a,b⟩
  dsimp
  push_cast
  rw [mul_div_mul_comm, Rat.num_div_den, Rat.num_div_den]

theorem rat_neg : Computable (fun a : ℚ => -a) := by
  refine (rat_divNat.comp
    ((int_neg.comp rat_num).pair rat_den).to_comp).of_eq ?_
  intro a
  push_cast
  rw [neg_div, Rat.num_div_den]

theorem rat_pow_two : Computable (fun k : ℕ => (2:ℚ)^(-(k+1:ℤ))) := by
  have hpow : Primrec (fun k : ℕ => 2^(k+1)) :=
    Primrec₂.unpaired'.mp Nat.Primrec.pow |>.comp (const 2) Primrec.succ
  refine (rat_divNat.comp ((Computable.const 1).pair hpow.to_comp)).of_eq ?_
  intro k
  dsimp
  push_cast
  change (1:ℚ)/(2:ℚ)^(k+1) = (2:ℚ)^(-(k+1:ℤ))
  rw [show (-(k+1:ℤ)) = -((k+1:ℕ):ℤ) by omega, zpow_neg, zpow_natCast, one_div]


theorem rat_natCast : Computable (fun n : ℕ => (n:ℚ)) := by
  refine (rat_divNat.comp (int_ofNat.to_comp.pair (Computable.const 1))).of_eq ?_
  intro n
  simp

def floorNat (q : ℚ) : ℕ := q.num.toNat / q.den

theorem floorNat_computable : Primrec floorNat :=
  nat_div.comp (int_toNat.comp rat_num) rat_den

theorem floorNat_eq (q : ℚ) (m : ℕ) (hl : (m:ℚ) ≤ q) (hu : q < (m:ℚ)+1) :
    floorNat q = m := by
  have hd : (0:ℚ) < q.den := by exact_mod_cast q.pos
  have hlo : (m:ℚ) * q.den ≤ q.num := by
    have h := (le_div_iff₀ hd).mp (hl.trans_eq (Rat.num_div_den q).symm)
    exact h
  have hhi : (q.num:ℚ) < ((m:ℚ)+1) * q.den := by
    exact (div_lt_iff₀ hd).mp ((Rat.num_div_den q).trans_lt hu)
  have hn : 0 ≤ q.num := by
    have : (0:ℚ) ≤ q.num := (by positivity : (0:ℚ) ≤ (m:ℚ)*q.den).trans hlo
    exact_mod_cast this
  have hcast := Int.toNat_of_nonneg hn
  apply Nat.div_eq_of_lt_le
  · have hz : (m:ℤ) * q.den ≤ q.num := by exact_mod_cast hlo
    rw [← hcast] at hz
    exact_mod_cast hz
  · have hz : q.num < ((m:ℤ)+1) * q.den := by exact_mod_cast hhi
    rw [← hcast] at hz
    exact_mod_cast hz

end Sigma2.UpperCoding
