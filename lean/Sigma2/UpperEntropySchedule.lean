import Sigma2.UpperEntropyApproximation

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Sigma2.UpperEntropySchedule
open UpperEntropyTruncation UpperEntropyApproximation UpperFiniteBorn UpperFiniteAmplitudes
open UpperFiniteOperators UpperEntropyFinite

/-- One integer budget covers entropy and the game-dependent loss factor. -/
def stageIndex (B t : ℕ) : ℕ := stageDimension B ((B+1)*(t+1))

theorem stageIndex_primrec : Primrec (fun p : ℕ × ℕ => stageIndex p.1 p.2) := by
  have hr : Primrec (fun p : ℕ × ℕ => (p.1+1)*(p.2+1)) := by fun_prop
  exact stageDimension_primrec.comp (Primrec.fst.pair hr)

/-- Scheduled finite data use the original entropy slack. -/
def ScheduledData (G : Game) (B : ℕ) : Prop := ∀ t,
  ∃ z : Data G.scenario (stageIndex B t+1),
    Feasible G (stageIndex B t+1) (1/(t+1:ℝ)) z ∧
      (∑ i,entropyTerm (z.1 i)) ≤ (B:ℝ)+1/(stageIndex B t+1:ℝ)

theorem mass_lower (p : ℕ → ℝ) (hp : ∀ i,0 ≤ p i) (hs : Summable p)
    (ht : (∑' i,p i)=1) (ha : Antitone p)
    (hH : Summable (fun i => entropyTerm (p i))) (B t : ℕ)
    (hB : (∑' i,entropyTerm (p i)) ≤ B) :
    1/2 ≤ mass p (stageIndex B t+1) := by
  have hh := scheduled_tail p hp hs ht ha hH B ((B+1)*(t+1)) hB
  have hr : (1:ℝ) ≤ ((B+1)*(t+1):ℕ) := by exact_mod_cast (Nat.mul_pos (Nat.succ_pos B) (Nat.succ_pos t))
  have hsmall : (1:ℝ)/(((B+1)*(t+1):ℕ)+1:ℝ)^2 ≤ 1/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hsplit := hs.sum_add_tsum_nat_add (stageIndex B t+1)
  rw [ht,← Fin.sum_univ_eq_sum_range] at hsplit
  change mass p (stageIndex B t+1)+(∑' i,p (i+(stageIndex B t+1)))=1 at hsplit
  have htail : (∑' i,p (i+(stageIndex B t+1))) ≤ 1/4 := by
    simpa only [stageIndex,Nat.add_assoc] using hh.trans hsmall
  linarith

theorem scheduled_loss_bound (B t C : ℕ) (hC : 2*C ≤ B) :
    (2*C:ℝ)/(((B+1)*(t+1):ℕ)+1:ℝ)^2 ≤ 1/(t+1:ℝ) := by
  have ht : (0:ℝ) < t+1 := by positivity
  have hr : (0:ℝ) ≤ ((B+1)*(t+1):ℕ) := Nat.cast_nonneg _
  have hmul : (2*C:ℝ)*(t+1) ≤ ((B+1)*(t+1):ℕ) := by
    push_cast
    apply mul_le_mul_of_nonneg_right _ ht.le
    exact_mod_cast hC.trans (Nat.le_succ B)
  apply (div_le_div_iff₀ (by positivity) ht).mpr
  nlinarith

/-- Compression preserves the true truncated Born probabilities and entropy. -/
theorem truncated_data (G : Game) (S : PureStrategy G.scenario)
    (p : ℕ → ℝ) (hp : ∀ i,0 ≤ p i) (hs : Summable p) (ht : (∑' i,p i)=1)
    (ha : Antitone p) (hH : Summable (fun i => entropyTerm (p i)))
    (hv : S.vector=UpperSchmidtState.vector p hp hs) (hS : Perfect G (normalOfPure S))
    (m : ℕ) (hm : 1/2 ≤ mass p m) (η : ℝ)
    (hη : (answerPairs G:ℝ)*(2*(∑' i,p (i+m))) ≤ η) :
    ∃ z : Data G.scenario m,Feasible G m η z ∧
      (∑ i,entropyTerm (z.1 i)) ≤ 2*(∑' i,entropyTerm (p i))+1/Real.log 2 := by
  have hpos : 0 < mass p m := by linarith
  obtain ⟨hpn,hps,hpa⟩ := normalized_simplex p hp ha m hpos
  let q := pad m (probabilities p m)
  have hq := pad_nonneg m (probabilities p m) hpn
  have hqs := pad_summable m (probabilities p m)
  have hqt : (∑' i,q i)=1 := (pad_sum _ _).trans hps
  let w := UpperSchmidtState.vector q hq hqs
  have hw : ‖w‖=1 := UpperSchmidtState.vector_unit q hq hqs hqt
  let T : PureStrategy G.scenario := ⟨S.measurements,w,hw⟩
  have herr := loss_error G S hS w hw
  rw [hv] at herr
  have hnorm := truncation_norm_sq p hp hs ht ha m hpos
  have hl : loss G (normalOfPure T) ≤ η := herr.trans
    ((mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg (answerPairs G))).trans hη)
  let t : Fin m → ℝ := fun i => Real.sqrt (probabilities p m i)
  have hpad i : pad m t i=Real.sqrt (q i) := by
    by_cases hi : i<m <;> simp [q,t,pad,hi]
  have hvec i j : T.vector (i,j)=if i=j then (pad m t i:ℂ) else 0 := by
    change UpperSchmidtState.vector q hq hqs (i,j)=_
    rw [UpperSchmidtState.vector_apply,hpad]
  let z : Data G.scenario m := (probabilities p m,t,
    fun x a => compress m (S.measurements.alice x a),
    fun y b => compress m (S.measurements.bob y b))
  refine ⟨z,⟨hpn,hps,hpa,(fun i => ⟨Real.sqrt_nonneg _,Real.sq_sqrt (hpn i)⟩),
    (fun x a => compress_positive _ _ (S.measurements.alice_pos x a)),
    (fun y b => compress_positive _ _ (S.measurements.bob_pos y b)),
    (fun x => compress_sum _ _ (S.measurements.alice_sum x)),
    (fun y => compress_sum _ _ (S.measurements.bob_sum y)),?_⟩,
    entropy_bound p hp hs ht hH m hm⟩
  exact (diagonal_loss G T m t hvec).symm.trans_le hl

/-- Finite-entropy perfection supplies every stage of one computable schedule. -/
theorem scheduled_of_perfect (G : Game) (hG : HasFiniteEntropyPerfect G) :
    ∃ B,ScheduledData G B := by
  obtain ⟨S,hS,hA,hB,hmA,hmB,hEA,hEB⟩ :=
    Preliminaries.finite_entropy_pure_component G |>.mp hG
  obtain ⟨p,u,hp,hs,ht,hu,he,hH,ha⟩ := EntropyEnumeration.ordered_entropy_witness hA hEA
  have he' : ∀ v,(UpperSchmidtSpectrum.density S.vector S.unit).op v=
      ∑' i,((p i:ℂ)*inner ℂ (u i) v) • u i := by
    rw [← marginal_op_eq S hA hmA]
    exact he
  obtain ⟨T,hTv,hprob⟩ := UpperSchmidtState.exists_strategy S p u hp hs ht hu he'
  have hT : Perfect G (normalOfPure T) := by
    unfold Perfect loss at *
    simpa only [normalOfPure_probability,hprob] using hS
  let H := ∑' i,entropyTerm (p i)
  obtain ⟨B,hbudget⟩ := exists_nat_ge
    (max (2*H+1/Real.log 2) (max H (2*(answerPairs G:ℝ))))
  have hnorm : 2*H+1/Real.log 2 ≤ B := (le_max_left _ _).trans hbudget
  have hB : H ≤ B := (le_max_left _ _).trans ((le_max_right _ _).trans hbudget)
  have hfactor : 2*answerPairs G ≤ B := by
    exact_mod_cast (le_max_right H (2*(answerPairs G:ℝ))).trans
      ((le_max_right _ _).trans hbudget)
  refine ⟨B,fun t => ?_⟩
  have hm := mass_lower p hp hs ht ha hH B t hB
  have htail := scheduled_tail p hp hs ht ha hH B ((B+1)*(t+1)) hB
  have hl : (answerPairs G:ℝ)*(2*(∑' i,p (i+(stageIndex B t+1)))) ≤ 1/(t+1:ℝ) := by
    calc
      _ ≤ (answerPairs G:ℝ)*(2*(1/(((B+1)*(t+1):ℕ)+1:ℝ)^2)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [stageIndex,Nat.add_assoc] using htail
      _ = (2*answerPairs G:ℝ)/(((B+1)*(t+1):ℕ)+1:ℝ)^2 := by ring
      _ ≤ 1/(t+1:ℝ) := scheduled_loss_bound B t _ hfactor
  obtain ⟨z,hf,he⟩ := truncated_data G T p hp hs ht ha hH hTv hT
    (stageIndex B t+1) hm (1/(t+1:ℝ)) hl
  exact ⟨z,hf,he.trans (hnorm.trans (le_add_of_nonneg_right (by positivity)))⟩

end Sigma2.UpperEntropySchedule
