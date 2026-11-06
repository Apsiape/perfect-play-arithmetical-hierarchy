import Sigma2.Preliminaries

noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerAlgebra

theorem op_smul_zero (c : ℂ) : c • (0:Op)=0 := by
  apply ContinuousLinearMap.ext
  intro z
  ext k
  change c*(0:ℂ)=0
  exact mul_zero c

theorem op_star_sum {ι : Type} [Fintype ι] (f : ι → Op) :
    star (∑ i,f i)=∑ i,star (f i) := by
  exact map_sum (starAddEquiv : Op ≃+ Op) f Finset.univ

theorem triangle_product (u v w : Op)
    (hu : Unitary u) (hv : Unitary v) (hw : Unitary w)
    (htri : let P : Matrix (Fin 3) (Fin 3) Op :=
      !![(1/3:ℂ) • (1:Op), (1/3:ℂ) • u, (1/3:ℂ) • w;
         (1/3:ℂ) • star u, (1/3:ℂ) • (1:Op), (1/3:ℂ) • v;
         (1/3:ℂ) • star w, (1/3:ℂ) • star v, (1/3:ℂ) • (1:Op)]
      P*P=P) : w=u*v := by
  have h := congrArg (fun P : Matrix (Fin 3) (Fin 3) Op => P 0 2) htri
  norm_num [Matrix.mul_apply, Fin.sum_univ_three] at h
  simp only [smul_mul_smul_comm,smul_smul] at h
  apply sub_eq_zero.mp
  have he : w-u*v = (9:ℂ) •
      ((1/3:ℂ) • w - ((1/9:ℂ) • w + (1/9:ℂ) • (u*v) + (1/9:ℂ) • w)) := by module
  rw [he, ← h]
  module

theorem graph_linear_row {n} (q : Fin n → ℚ) (U : Fin n → Op)
    (hU : ∀ i, Unitary (U i)) :
    (∑ i, (q i:ℂ) • U i)=0 ↔
      (∑ i, (q i:ℂ) • (!![(0:Op),U i;star (U i),0] : Matrix (Fin 2) (Fin 2) Op))=0 := by
  constructor
  · intro h
    have hs := congrArg star h
    have hs' : (∑ i, (q i:ℂ) • star (U i))=0 := by
      calc
        _ = star (∑ i, (q i:ℂ) • U i) := by
          rw [op_star_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [star_smul,star_ratCast]
        _ = 0 := (congrArg (fun A : Op => star A) h).trans (star_zero Op)
    apply Matrix.ext
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.sum_apply, Matrix.smul_apply, h, hs',op_smul_zero]
  · intro h
    have hh := congrArg (fun P : Matrix (Fin 2) (Fin 2) Op => P 0 1) h
    simpa [Matrix.sum_apply,Matrix.smul_apply] using hh

theorem row_column_overlap {d : ℕ} (hd : 0<d) (V : Fin d → Op)
    (hV : ∀ j, Unitary (V j)) :
    let C : Matrix (Fin d) (Fin d) Op := fun i j => (1/(d:ℂ)) • (V i*star (V j))
    let R : Matrix (Fin d) (Fin d) Op := fun _ _ => (1/(d:ℂ)) • (1:Op)
    C*R=0 ↔ (∑ j, V j)=0 := by
  classical
  let c : ℂ := 1/(d:ℂ)
  have hc : c≠0 := by dsimp [c]; exact one_div_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  let C : Matrix (Fin d) (Fin d) Op := Matrix.of (fun i j => c • (V i*star (V j)))
  let R : Matrix (Fin d) (Fin d) Op := Matrix.of (fun _ _ => c • (1:Op))
  have hentry (i j : Fin d) : (C*R) i j = (c*c) • (V i * star (∑ k,V k)) := by
    rw [Matrix.mul_apply]
    simp only [C,R,Matrix.of_apply,smul_mul_smul_comm,mul_one,
      ← Finset.smul_sum, ← Finset.mul_sum, op_star_sum]
  change C*R=0 ↔ _
  constructor
  · intro h
    let i : Fin d := ⟨0,hd⟩
    have hz := congrArg (fun P : Matrix (Fin d) (Fin d) Op => P i i) h
    rw [hentry] at hz
    change (c*c) • (V i * star (∑ k,V k))=0 at hz
    have hz' : V i * star (∑ k,V k)=0 := (smul_eq_zero.mp hz).resolve_left (mul_ne_zero hc hc)
    have hh := congrArg (fun A : Op => star (V i)*A) hz'
    rw [← mul_assoc,(hV i).1,one_mul,mul_zero] at hh
    exact star_eq_zero.mp hh
  · intro h
    apply Matrix.ext
    intro i j
    rw [hentry,h]
    exact (congrArg (fun A : Op => (c*c) • (V i * A)) (star_zero Op)).trans (by simp only [mul_zero,smul_zero]; rfl)

theorem trace_smul (c : ℂ) (A : Op) : trace (c • A)=c*trace A := by
  simp only [trace,entry,ContinuousLinearMap.smul_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  exact tsum_mul_left

theorem row_loss_formula (L d : ℕ) (hd : 0<d) (S : Op) (hS : star S=S)
    (h : Density) (hs : Centralizes h.op S)
    (V : Fin d → Op) (hV : ∀ j, Unitary (V j))
    (hslots : ∑ j, V j=(2*(L:ℂ)) • S) :
    (1/(d:ℝ)^3) * (trace (h.op*(star (∑ j,V j)*(∑ j,V j)))).re =
      4*(L:ℝ)^2/(d:ℝ)^3 * (trace (h.op*(S*S))).re := by
  have hop : star (∑ j,V j)*(∑ j,V j)= (4*(L:ℂ)^2) • (S*S) := by
    rw [hslots,star_smul,hS]
    simp only [star_mul,star_ofNat,star_natCast,smul_mul_smul_comm]
    congr 1
    ring
  rw [hop,mul_smul_comm,trace_smul]
  have hc : (4*(L:ℂ)^2)=((4*(L:ℝ)^2:ℝ):ℂ) := by push_cast; rfl
  rw [hc,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

#print axioms triangle_product
#print axioms graph_linear_row
#print axioms row_column_overlap
#print axioms row_loss_formula
end Sigma2.CompilerAlgebra
