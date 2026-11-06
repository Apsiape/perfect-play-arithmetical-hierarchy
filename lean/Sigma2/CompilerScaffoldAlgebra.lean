import Sigma2.CompilerScaffold

noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerScaffold

def evalWord (U : ℕ → Op) : Word → Op
  | [] => 1
  | t::w => (if t.2 then star (U t.1) else U t.1) * evalWord U w

def evalPoly (U : ℕ → Op) (p : Poly) : Op :=
  (p.map (fun t => (t.1:ℂ) • evalWord U t.2)).sum

theorem evalWord_append (U : ℕ → Op) (u v : Word) :
    evalWord U (u++v)=evalWord U u*evalWord U v := by
  induction u with
  | nil => simp [evalWord]
  | cons t u ih => simp [evalWord,ih,mul_assoc]

theorem evalWord_adj (U : ℕ → Op) (w : Word) :
    evalWord U (adjWord w)=star (evalWord U w) := by
  induction w with
  | nil => simp [adjWord,evalWord]
  | cons t w ih =>
    simp only [adjWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil]
    rw [evalWord_append]
    change evalWord U (adjWord w) * evalWord U [(t.1,!t.2)]=_
    rw [ih]
    cases t with
    | mk i b => cases b <;> simp [evalWord,star_mul]

theorem evalPoly_append (U : ℕ → Op) (p q : Poly) :
    evalPoly U (p++q)=evalPoly U p+evalPoly U q := by
  simp [evalPoly]

theorem evalPoly_scale (U : ℕ → Op) (c : ℚ) (p : Poly) :
    evalPoly U (scale c p)=(c:ℂ) • evalPoly U p := by
  induction p with
  | nil =>
    change (0:Op)=(c:ℂ) • (0:Op)
    exact (CompilerAlgebra.op_smul_zero _).symm
  | cons t p ih =>
    change ((c*t.1:ℚ):ℂ) • evalWord U t.2+evalPoly U (scale c p)=
      (c:ℂ) • ((t.1:ℂ) • evalWord U t.2+evalPoly U p)
    rw [ih,Rat.cast_mul,smul_add,mul_smul]

theorem evalPoly_sub (U : ℕ → Op) (p q : Poly) :
    evalPoly U (sub p q)=evalPoly U p-evalPoly U q := by
  rw [sub,evalPoly_append,evalPoly_scale]
  push_cast
  module

/-- The K1 finite polynomial expansion retains the actual rational coefficients. -/
theorem evalPoly_mul (U : ℕ → Op) (p q : Poly) :
    evalPoly U (mul p q)=evalPoly U p*evalPoly U q := by
  have inner (t : ℚ × Word) :
      evalPoly U (q.map (fun u => (t.1*u.1,t.2++u.2)))=
        ((t.1:ℂ) • evalWord U t.2)*evalPoly U q := by
    induction q with
    | nil => simp [evalPoly]
    | cons u q ih =>
      simp only [List.map_cons,evalPoly,List.sum_cons] at ih ⊢
      rw [evalWord_append,Rat.cast_mul,mul_add,← ih]
      congr 1
      simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
      congr 1
      ring
  induction p with
  | nil => simp [mul,evalPoly]
  | cons t p ih =>
    change evalPoly U (q.map (fun u => (t.1*u.1,t.2++u.2)) ++ mul p q)=_
    rw [evalPoly_append,inner,ih]
    simp [evalPoly,add_mul]

theorem evalPoly_expression (P : Presentation) (U : ℕ → Op) (r : ℕ) (p : Expr) :
    evalPoly U (expression P r p)=
      p.eval (evalPoly U (e r)) (fun i => evalPoly U (labelCopy P r i)) := by
  induction p with
  | scalar c => exact evalPoly_scale U c (e r)
  | label i => rfl
  | add p q hp hq => simp [expression,Expr.eval,evalPoly_append,hp,hq]
  | mul p q hp hq => simp [expression,Expr.eval,evalPoly_mul,hp,hq]
  | adj p hp =>
    have ha (q : Poly) : evalPoly U (adj q)=star (evalPoly U q) := by
      induction q with
      | nil =>
        change (0:Op)=star (0:Op)
        exact (star_zero Op).symm
      | cons t q ih =>
        change (t.1:ℂ) • evalWord U (adjWord t.2)+evalPoly U (adj q)=
          star ((t.1:ℂ) • evalWord U t.2+evalPoly U q)
        rw [evalWord_adj,ih,star_add ((t.1:ℂ) • evalWord U t.2) (evalPoly U q),
          star_smul,star_ratCast]
    simpa [expression,Expr.eval,hp] using ha (expression P r p)

end Sigma2.CompilerScaffold
