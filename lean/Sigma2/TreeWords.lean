import Sigma2.FockTrace
import Sigma2.TreeTail
import Sigma2.ProjectionSeries
noncomputable section
open scoped BigOperators
namespace Sigma2.Tree
abbrev Word := List (Fin 4)

def wordOp {P} (R : NormalRealization P) : Word → Op
  | [] => R.support
  | a::w => R.creation a * wordOp R w

def wordProjection {P} (R : NormalRealization P) (w : Word) : Op :=
  wordOp R w * R.label P.root * star (wordOp R w)

def depthProjection {P} (R : NormalRealization P) (m : ℕ) : Op :=
  ∑ w ∈ (Finset.univ : Finset (Fin m → Fin 4)),
    let A := wordOp R (List.ofFn w)
    A*star A

/-- Creation words remain supported isometries on the actual state support. -/
theorem word_supported {P} (R : NormalRealization P) (w : Word) :
    R.support*wordOp R w=wordOp R w ∧ wordOp R w*R.support=wordOp R w := by
  induction w with
  | nil => exact ⟨R.support_projection.2,R.support_projection.2⟩
  | cons a w ih =>
    constructor
    · change R.support*(R.creation a*wordOp R w)=R.creation a*wordOp R w
      rw [← mul_assoc,(R.creation_supported a).1]
    · change (R.creation a*wordOp R w)*R.support=R.creation a*wordOp R w
      rw [mul_assoc,ih.2]

theorem word_isometry {P} (R : NormalRealization P) (w : Word) :
    star (wordOp R w)*wordOp R w=R.support := by
  induction w with
  | nil => exact (congrArg (fun A : Op => A*R.support) R.support_projection.1).trans R.support_projection.2
  | cons a w ih =>
    change star (R.creation a*wordOp R w)*(R.creation a*wordOp R w)=_
    rw [star_mul]
    calc
      _ = star (wordOp R w)*(star (R.creation a)*R.creation a)*wordOp R w := by noncomm_ring
      _ = _ := by rw [R.isometries a a,if_pos rfl,mul_assoc,(word_supported R w).1,ih]

theorem word_eq_foldr {P} (R : NormalRealization P) (w : Word) :
    wordOp R w=w.foldr (fun a A => R.creation a*A) R.support := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [wordOp,List.foldr_cons,ih]

/-- Eqs. (30)-(31): the exact trace of every depth tail. -/
theorem depth_trace {P} (R : NormalRealization P) (m : ℕ) :
    (trace (R.density.op*depthProjection R m)).re=(1/4:ℝ)^m := by
  have hcov (w : Word) : R.density.op*wordOp R w=
      ((1/16:ℂ)^w.length) • (wordOp R w*R.density.op) := by
    rw [word_eq_foldr]
    exact TreeBasic.word_covariance R w
  have ht (w : Fin m → Fin 4) :
      trace (R.density.op*(wordOp R (List.ofFn w)*star (wordOp R (List.ofFn w))))=
        ((1/16:ℂ)^m)*trace R.density.op := by
    rw [← mul_assoc,hcov,smul_mul_assoc,CompilerAlgebra.trace_smul,
      FockTrace.isometry_trace R _ (word_isometry R _),List.length_ofFn]
  have hh : trace (R.density.op*depthProjection R m)=
      ((1/4:ℂ)^m)*trace R.density.op := by
    unfold depthProjection
    rw [FockTrace.trace_density_sum]
    · simp_rw [ht]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      calc
        _ = ((4:ℂ)*(1/16:ℂ))^m*trace R.density.op := by rw [mul_pow]; ring
        _ = _ := by norm_num
    · intro w _
      exact ContinuousLinearMap.isPositive_self_comp_adjoint _
  rw [hh]
  have hc : (1/4:ℂ)^m=(((1/4:ℝ)^m:ℝ):ℂ) := by push_cast; rfl
  rw [hc,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    FockTrace.trace_density_re,mul_one]

#print axioms word_isometry
#print axioms depth_trace
/-- The root is orthogonal to every creation range. -/
theorem root_creation_zero {P} (R : NormalRealization P) (a : Fin 4) :
    R.label P.root*R.creation a=0 ∧ star (R.creation a)*R.label P.root=0 := by
  have hsum : (∑ b,R.creation b*star (R.creation b))*R.creation a=R.creation a := by
    rw [Finset.sum_mul]
    calc
      _ = ∑ b,R.creation b*(if b=a then R.support else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [mul_assoc,R.isometries b a]
      _ = R.creation a := by
        simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_pos,
          (R.creation_supported a).2]
  rw [R.ranges,sub_mul,(R.creation_supported a).1] at hsum
  have hz : R.label P.root*R.creation a=0 := sub_eq_self.mp hsum
  refine ⟨hz,?_⟩
  have hh := congrArg star hz
  have hpstar : star (R.label P.root)=R.label P.root := by
    have hs := congrArg star R.ranges
    have he : star (∑ b,R.creation b*star (R.creation b))=∑ b,R.creation b*star (R.creation b) := by
      rw [CompilerAlgebra.op_star_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [star_mul,star_star]
    rw [he,star_sub R.support (R.label P.root),R.support_projection.1,R.ranges] at hs
    exact sub_right_inj.mp hs.symm
  simpa only [star_mul,hpstar,star_zero Op] using hh

/-- Distinct root-word sectors are orthogonal, including unequal word lengths. -/
theorem word_root_inner {P} (hP : P.admissible) (R : NormalRealization P) (w u : Word) :
    R.label P.root*star (wordOp R w)*wordOp R u*R.label P.root=
      if w=u then R.label P.root else 0 := by
  have hp := TreeFoundation.root_projection hP R
  induction w generalizing u with
  | nil =>
    cases u with
    | nil =>
      simp only [wordOp,R.support_projection.1,(R.label_supported P.root).1,
        (R.label_supported P.root).2,hp.2,ite_true]
    | cons b u =>
      have hne : ([] : Word)≠b::u := by intro h; cases h
      simp only [wordOp,R.support_projection.1,if_neg hne]
      calc
        _ = (R.label P.root*R.creation b)*wordOp R u*R.label P.root := by
          rw [(R.label_supported P.root).2]
          noncomm_ring
        _ = 0 := by rw [(root_creation_zero R b).1,zero_mul,zero_mul]
  | cons a w ih =>
    cases u with
    | nil =>
      simp only [wordOp,star_mul,List.cons_ne_nil,if_false]
      calc
        _ = R.label P.root*star (wordOp R w)*(star (R.creation a)*(R.support*R.label P.root)) := by noncomm_ring
        _ = 0 := by rw [(R.label_supported P.root).1,(root_creation_zero R a).2,mul_zero]
    | cons b u =>
      simp only [wordOp,star_mul]
      have he : R.label P.root*(star (wordOp R w)*star (R.creation a))*(R.creation b*wordOp R u)*R.label P.root=
          R.label P.root*star (wordOp R w)*(star (R.creation a)*R.creation b)*wordOp R u*R.label P.root := by noncomm_ring
      rw [he]
      by_cases hab : a=b
      · subst b
        rw [R.isometries a a,if_pos rfl]
        have hs : R.label P.root*star (wordOp R w)*R.support*wordOp R u*R.label P.root=
            R.label P.root*star (wordOp R w)*wordOp R u*R.label P.root := by
          rw [mul_assoc _ R.support (wordOp R u),(word_supported R u).1]
        rw [hs,ih]
        simp
      · have hne : a::w≠b::u := fun hh => hab (List.cons.inj hh).1
        rw [R.isometries a b,if_neg hab,if_neg hne]
        simp

theorem word_projection {P} (hP : P.admissible) (R : NormalRealization P) (w : Word) :
    Projection (wordProjection R w) := by
  have hp := TreeFoundation.root_projection hP R
  constructor
  · unfold wordProjection
    rw [star_mul,star_mul,star_star,hp.1]
    noncomm_ring
  · unfold wordProjection
    calc
      _ = wordOp R w*(R.label P.root*star (wordOp R w)*wordOp R w*R.label P.root)*star (wordOp R w) := by noncomm_ring
      _ = _ := by rw [word_root_inner hP R w w,if_pos rfl]

theorem word_projection_orthogonal {P} (hP : P.admissible) (R : NormalRealization P)
    (w u : Word) (hwu : w≠u) : wordProjection R w*wordProjection R u=0 := by
  unfold wordProjection
  calc
    _ = wordOp R w*(R.label P.root*star (wordOp R w)*wordOp R u*R.label P.root)*star (wordOp R u) := by noncomm_ring
    _ = 0 := by rw [word_root_inner hP R w u,if_neg hwu,mul_zero,zero_mul]

theorem word_partition_summable {P} (hP : P.admissible) (R : NormalRealization P) (v : H) :
    Summable (fun w : Word => wordProjection R w v) :=
  ProjectionSeries.summable (wordProjection R) (word_projection hP R) (word_projection_orthogonal hP R) v

/-- Split a finite word sum at its first letter, without choosing an enumeration of all words. -/
theorem sum_words_succ (f : Word → Op) (m : ℕ) :
    (∑ u : Fin (m+1) → Fin 4,f (List.ofFn u))=
      ∑ a : Fin 4,∑ u : Fin m → Fin 4,f (a::List.ofFn u) := by
  have hh := (Fin.consEquiv (fun _ : Fin (m+1) => Fin 4)).sum_comp
    (fun u => f (List.ofFn u))
  rw [Fintype.sum_prod_type] at hh
  change (∑ a : Fin 4,∑ u : Fin m → Fin 4,f (List.ofFn (Fin.cons a u)))=
    (∑ u : Fin (m+1) → Fin 4,f (List.ofFn u)) at hh
  simpa only [List.ofFn_cons] using hh.symm

def levelProjection {P} (R : NormalRealization P) (m : ℕ) : Op :=
  ∑ u : Fin m → Fin 4,wordProjection R (List.ofFn u)

theorem word_range_cons {P} (R : NormalRealization P) (a : Fin 4) (w : Word) :
    wordOp R (a::w)*star (wordOp R (a::w))=
      R.creation a*(wordOp R w*star (wordOp R w))*star (R.creation a) := by
  simp only [wordOp,star_mul]
  noncomm_ring

theorem word_projection_cons {P} (R : NormalRealization P) (a : Fin 4) (w : Word) :
    wordProjection R (a::w)=R.creation a*wordProjection R w*star (R.creation a) := by
  simp only [wordProjection,wordOp,star_mul]
  noncomm_ring

theorem depth_eq_tail {P} (R : NormalRealization P) (m : ℕ) :
    depthProjection R m=TreeTail.tail R m := by
  induction m with
  | zero =>
    simp only [depthProjection,List.ofFn_zero,wordOp,R.support_projection.1,R.support_projection.2,
      Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,one_smul,TreeTail.tail]
  | succ m ih =>
    change (∑ u : Fin (m+1) → Fin 4,wordOp R (List.ofFn u)*star (wordOp R (List.ofFn u)))=_
    rw [sum_words_succ (fun w => wordOp R w*star (wordOp R w)) m]
    simp_rw [word_range_cons]
    change (∑ a,∑ u : Fin m → Fin 4,R.creation a*(wordOp R (List.ofFn u)*star (wordOp R (List.ofFn u)))*star (R.creation a))=_
    simp_rw [← Finset.sum_mul,← Finset.mul_sum]
    change TreeTail.step R (depthProjection R m)=TreeTail.step R (TreeTail.tail R m)
    rw [ih]

theorem level_eq_tail_difference {P} (R : NormalRealization P) (m : ℕ) :
    levelProjection R m=TreeTail.tail R m-TreeTail.tail R (m+1) := by
  induction m with
  | zero =>
    have he : levelProjection R 0=R.label P.root := by
      simp only [levelProjection,List.ofFn_zero,wordProjection,wordOp,R.support_projection.1,
        (R.label_supported P.root).1,(R.label_supported P.root).2,
        Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,one_smul]
    rw [he]
    change R.label P.root=R.support-∑ a,R.creation a*R.support*star (R.creation a)
    simp_rw [(R.creation_supported _).2]
    rw [R.ranges]
    abel
  | succ m ih =>
    have he : levelProjection R (m+1)=TreeTail.step R (levelProjection R m) := by
      unfold levelProjection
      rw [sum_words_succ (wordProjection R) m]
      simp_rw [word_projection_cons]
      unfold TreeTail.step
      simp only [Finset.mul_sum,Finset.sum_mul]
    rw [he,ih]
    change TreeTail.step R (TreeTail.tail R m-TreeTail.tail R (m+1))=
      TreeTail.step R (TreeTail.tail R m)-TreeTail.step R (TreeTail.tail R (m+1))
    unfold TreeTail.step
    simp only [mul_sub,sub_mul,Finset.sum_sub_distrib]

/-- The complete countable word partition, with unconditional summability. -/
theorem word_partition {P} (hP : P.admissible) (R : NormalRealization P) (v : H) :
    (∑' w : Word,wordProjection R w v)=R.support v := by
  have hw := word_partition_summable hP R v
  have hs : Summable (fun p : Σ m : ℕ,Fin m → Fin 4 => wordProjection R (List.ofFn p.2) v) :=
    List.equivSigmaTuple.symm.summable_iff.mpr hw
  have he (m : ℕ) : (∑' u : Fin m → Fin 4,wordProjection R (List.ofFn u) v)=
      TreeTail.tail R m v-TreeTail.tail R (m+1) v := by
    rw [tsum_fintype]
    have hh := congrArg (fun A : Op => A v) (level_eq_tail_difference R m)
    simpa only [levelProjection,ContinuousLinearMap.sum_apply,sub_apply] using hh
  have hgroup := hs.sigma
  simp_rw [he] at hgroup
  have hlim := hgroup.hasSum.tendsto_sum_nat
  have hfinite (m : ℕ) :
      (∑ n ∈ Finset.range m,(TreeTail.tail R n v-TreeTail.tail R (n+1) v))=
        R.support v-TreeTail.tail R m v := by
    rw [Finset.sum_range_sub']
    rfl
  simp_rw [hfinite] at hlim
  have hz : Filter.Tendsto (fun m => R.support v-TreeTail.tail R m v)
      Filter.atTop (nhds (R.support v)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (TreeTail.strong_tail_zero R v)
  have htotal := tendsto_nhds_unique hlim hz
  calc
    _ = ∑' p : Σ m : ℕ,Fin m → Fin 4,wordProjection R (List.ofFn p.2) v :=
      (List.equivSigmaTuple.symm.tsum_eq (fun w => wordProjection R w v)).symm
    _ = ∑' m,∑' u : Fin m → Fin 4,wordProjection R (List.ofFn u) v := hs.tsum_sigma
    _ = ∑' m,(TreeTail.tail R m v-TreeTail.tail R (m+1) v) := tsum_congr he
    _ = R.support v := htotal

#print axioms word_partition_summable
#print axioms depth_eq_tail
#print axioms word_partition
end Sigma2.Tree
