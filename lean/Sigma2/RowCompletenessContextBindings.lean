import Sigma2.RowCompletenessEffects

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns RowWalsh

theorem spectral_eigen (U : Op) (hs : star U=U) (hq : U*U=1) (b : Bool) :
    spectralEffect U b*U=sign b • spectralEffect U b := reflection_eigen U hs hq b

theorem spectral_action (A U : Op) (hs : star U=U) (hq : U*U=1) (s b : Bool)
    (he : A*U=sign s • A) : A*spectralEffect U b=if s=b then A else 0 :=
  reflection_action A U hs hq s b he

theorem commute_spectral (A U : Op) (hc : Commute A U) (b : Bool) :
    Commute A (spectralEffect U b) :=
  ((Commute.one_right A).add_right (hc.smul_right (sign b))).smul_right (1/2:ℂ)

theorem joint_eigen_first (U V : Op) (hs : star U=U) (hq : U*U=1) (hc : Commute U V)
    (b c : Bool) : (spectralEffect U b*spectralEffect V c)*U=
      sign b • (spectralEffect U b*spectralEffect V c) := by
  rw [mul_assoc,← (commute_spectral U V hc c).eq,← mul_assoc,spectral_eigen U hs hq b,smul_mul_assoc]

theorem joint_eigen_second (U V : Op) (hs : star V=V) (hq : V*V=1) (b c : Bool) :
    (spectralEffect U b*spectralEffect V c)*V=sign c • (spectralEffect U b*spectralEffect V c) := by
  rw [mul_assoc,spectral_eigen V hs hq c,mul_smul_comm]

theorem joint_eigen_product (U V : Op) (hsU : star U=U) (hsV : star V=V)
    (hqU : U*U=1) (hqV : V*V=1) (hc : Commute U V) (b c : Bool) :
    (spectralEffect U b*spectralEffect V c)*(U*V)=
      (sign b*sign c) • (spectralEffect U b*spectralEffect V c) := by
  rw [← mul_assoc,joint_eigen_first U V hsU hqU hc b c,smul_mul_assoc,
    joint_eigen_second U V hsV hqV b c,smul_smul]

/-- The third scalar cell is determined by the first two and the prescribed parity. -/
theorem third_factor (U V W : Op) (hq : W*W=1) (neg : Bool)
    (hp : U*(V*W)=sign neg • (1:Op)) : W=sign neg • (U*V) := by
  have he : U*V=sign neg • W := by
    calc
      U*V=(U*(V*W))*W := by rw [mul_assoc,mul_assoc,hq,mul_one]
      _ = (sign neg • (1:Op))*W := by rw [hp]
      _ = sign neg • W := by rw [smul_mul_assoc,one_mul]
  calc
    W=(sign neg*sign neg) • W := by rw [sign_sq,one_smul]
    _ = sign neg • (sign neg • W) := by rw [smul_smul]
    _ = sign neg • (U*V) := congrArg (fun A : Op => sign neg • A) he.symm

theorem joint_eigen_third (U V W : Op) (hsU : star U=U) (hsV : star V=V)
    (hqU : U*U=1) (hqV : V*V=1) (hqW : W*W=1) (hc : Commute U V)
    (neg b c : Bool) (hp : U*(V*W)=sign neg • (1:Op)) :
    (spectralEffect U b*spectralEffect V c)*W=
      sign (Bool.xor (Bool.xor b c) neg) • (spectralEffect U b*spectralEffect V c) := by
  rw [third_factor U V W hqW neg hp,mul_smul_comm,
    joint_eigen_product U V hsU hsV hqU hqV hc b c,smul_smul,sign_xor,sign_xor]
  congr 1
  ring

theorem encoded_cellSign_zero (neg b c : Bool) : cellSign neg (2*bit b+bit c) 0=b := by
  cases b <;> cases c <;> rfl

theorem encoded_cellSign_one (neg b c : Bool) : cellSign neg (2*bit b+bit c) 1=c := by
  cases b <;> cases c <;> rfl

theorem encoded_cellSign_two (neg b c : Bool) :
    cellSign neg (2*bit b+bit c) 2=Bool.xor (Bool.xor b c) neg := by
  cases b <;> cases c <;> cases neg <;> decide

/-- Every encoded context outcome has the exact eigenvalue read by the table. -/
theorem context_eigen (C : Fin 3 → Op) (neg : Bool)
    (hs : ∀ j,star (C j)=C j) (hq : ∀ j,C j*C j=1)
    (hc : Commute (C 0) (C 1)) (hp : C 0*(C 1*C 2)=sign neg • (1:Op))
    (b c : Bool) (j : Fin 3) :
    (spectralEffect (C 0) b*spectralEffect (C 1) c)*C j=
      sign (cellSign neg (2*bit b+bit c) j.val) • (spectralEffect (C 0) b*spectralEffect (C 1) c) := by
  fin_cases j
  · rw [encoded_cellSign_zero]
    exact joint_eigen_first _ _ (hs 0) (hq 0) hc b c
  · rw [encoded_cellSign_one]
    exact joint_eigen_second _ _ (hs 1) (hq 1) b c
  · rw [encoded_cellSign_two]
    exact joint_eigen_third _ _ _ (hs 0) (hs 1) (hq 0) (hq 1) (hq 2) hc neg b c hp

theorem context_binding_zero (C : Fin 3 → Op) (neg : Bool)
    (hs : ∀ j,star (C j)=C j) (hq : ∀ j,C j*C j=1)
    (hc : Commute (C 0) (C 1)) (hp : C 0*(C 1*C 2)=sign neg • (1:Op))
    (b c t : Bool) (j : Fin 3) (hne : cellSign neg (2*bit b+bit c) j.val≠t) :
    (spectralEffect (C 0) b*spectralEffect (C 1) c)*spectralEffect (C j) t=0 := by
  rw [spectral_action _ _ (hs j) (hq j) _ t (context_eigen C neg hs hq hc hp b c j),ite_eq_right hne]

theorem decode_line_answer (v : ℕ) (hv : v<4) : ∃ b c : Bool,v=2*bit b+bit c := by
  interval_cases v
  · exact ⟨false,false,rfl⟩
  · exact ⟨false,true,rfl⟩
  · exact ⟨true,false,rfl⟩
  · exact ⟨true,true,rfl⟩

theorem decode_cell_answer (v : ℕ) (hv : v<2) : ∃ b : Bool,v=bitAnswer b := by
  interval_cases v
  · exact ⟨true,rfl⟩
  · exact ⟨false,rfl⟩

def rowContext {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (col : Bool) (k : Fin 3) : Fin 3 → Op :=
  fun j => if col then rowMagic R g j k else rowMagic R g k j

theorem rowContext_eigen {s} (R : Rows s) (g : Fin (RowSlots.squares R))
    (col : Bool) (k : Fin 3) (b c : Bool) (j : Fin 3) :
    (spectralEffect (rowContext R g col k 0) b*spectralEffect (rowContext R g col k 1) c)*rowContext R g col k j=
      sign (cellSign (col && decide (k.val=2)) (2*bit b+bit c) j.val) •
        (spectralEffect (rowContext R g col k 0) b*spectralEffect (rowContext R g col k 1) c) := by
  have hr := rowMagic_relations R g
  apply context_eigen (rowContext R g col k) (col && decide (k.val=2))
  · intro j
    cases col
    · exact hr.selfadjoint k j
    · exact hr.selfadjoint j k
  · intro j
    cases col
    · exact hr.square k j
    · exact hr.square j k
  · cases col
    · exact hr.row_commute k 0 1
    · exact hr.col_commute 0 1 k
  · cases col
    · simpa [rowContext,sign] using hr.row_product k
    · simpa [rowContext,sign] using hr.col_product k

end Sigma2.RowCompleteness
