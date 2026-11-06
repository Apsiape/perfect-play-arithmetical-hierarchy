import Sigma2.TableauBasic

noncomputable section
open scoped BigOperators
namespace Sigma2.Tree

theorem coord_bounds (w : Word) : xCoord w < 2^w.length ∧ yCoord w < 2^w.length := by
  induction w with
  | nil => simp [xCoord,yCoord]
  | cons a w ih =>
    fin_cases a <;> simp only [xCoord,yCoord,List.length_cons,pow_succ] <;> norm_num <;> omega

theorem nextX_geometry (w : Word) :
    (nextX w).length=w.length ∧
    xCoord (nextX w)=(if xCoord w+1=2^w.length then 0 else xCoord w+1) ∧
    yCoord (nextX w)=yCoord w := by
  induction w with
  | nil => simp [nextX,xCoord,yCoord]
  | cons a w ih =>
    have hb := coord_bounds w
    fin_cases a <;>
      simp [nextX,xCoord,yCoord,List.length_cons,pow_succ,ih.1,ih.2.1,ih.2.2] <;>
      split_ifs at * <;> omega

theorem nextY_geometry (w : Word) :
    (nextY w).length=w.length ∧ xCoord (nextY w)=xCoord w ∧
    yCoord (nextY w)=(if yCoord w+1=2^w.length then 0 else yCoord w+1) := by
  induction w with
  | nil => simp [nextY,xCoord,yCoord]
  | cons a w ih =>
    have hb := coord_bounds w
    fin_cases a <;>
      simp [nextY,xCoord,yCoord,List.length_cons,pow_succ,ih.1,ih.2.1,ih.2.2] <;>
      split_ifs at * <;> omega

theorem word_ext_coords (w u : Word) (hl : w.length=u.length)
    (hx : xCoord w=xCoord u) (hy : yCoord w=yCoord u) : w=u := by
  induction w generalizing u with
  | nil => cases u <;> simp_all
  | cons a w ih =>
    cases u with
    | nil => simp at hl
    | cons b u =>
      have hlen : w.length=u.length := by simpa using hl
      have hab : a=b := by
        fin_cases a <;> fin_cases b <;> simp_all [xCoord,yCoord] <;> omega
      subst b
      have hxx : xCoord w=xCoord u := by simp only [xCoord] at hx; omega
      have hyy : yCoord w=yCoord u := by simp only [yCoord] at hy; omega
      rw [ih u hlen hxx hyy]

theorem word_of_coords (n x y : ℕ) (hx : x<2^n) (hy : y<2^n) :
    ∃ w : Word, w.length=n ∧ xCoord w=x ∧ yCoord w=y := by
  induction n generalizing x y with
  | zero =>
    have hxx : x=0 := by simpa using hx
    have hyy : y=0 := by simpa using hy
    exact ⟨[],rfl,hxx.symm,hyy.symm⟩
  | succ n ih =>
    have hx' : x/2<2^n := by rw [pow_succ] at hx; omega
    have hy' : y/2<2^n := by rw [pow_succ] at hy; omega
    obtain ⟨w,hl,hwx,hwy⟩ := ih (x/2) (y/2) hx' hy'
    let a : Fin 4 := ⟨2*(x%2)+y%2,by omega⟩
    refine ⟨a::w,by simp [hl],?_,?_⟩
    · simp only [xCoord,hwx,a]
      omega
    · simp only [yCoord,hwy,a]
      omega

theorem run_blank (M : Automaton) (pulse : ℕ → Bool) (t x : ℕ) (h : t<x) :
    run M pulse t x=1 := by
  induction t generalizing x with
  | zero => simp [run,show x≠0 by omega]
  | succ t ih =>
    have hx : x≠0 := by omega
    simp only [run,if_neg hx,ih (x-1) (by omega),ih x (by omega),ih (x+1) (by omega)]
    exact M.blank_quiescence _

end Sigma2.Tree
