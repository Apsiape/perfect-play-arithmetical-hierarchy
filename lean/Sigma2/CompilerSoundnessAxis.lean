import Sigma2.CompilerSoundnessBlockEquations

/-! Literal axis operators and the distinguished target compression. -/
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessAxis
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCopies CompilerSoundnessBlockEquations CompilerSoundnessBindings
  CompilerSoundnessPolynomials MagicCells MagicRelations PauliMatrixUnits FourUnits
  Preliminaries CoarseCells FiniteSpectral
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

def pure (E : SupportedScaffold P) (g : Fin 4) : PureStrategy (scenario P) :=
  Classical.choose (conditional_pure_model E.strategy (fmsInstance P g) (E.conditional g))

theorem pure_laws (E : SupportedScaffold P) (g : Fin 4) :
    ConditionalPerfect (normalOfPure (pure E g)) (fmsInstance P g) ∧
      (pure E g).measurements.alice=E.strategy.measurements.alice ∧
      MarginalA (normalOfPure (pure E g)) E.densityA := by
  have h := Classical.choose_spec (conditional_pure_model E.strategy (fmsInstance P g) (E.conditional g))
  exact ⟨h.1,h.2.1,h.2.2.1 E.densityA E.marginalA⟩

def magicSupport (E : SupportedScaffold P) (g : Fin 4) : Op :=
  rowActive (pure E g) (fmsInstance P g) E.supportA 0

def cell (E : SupportedScaffold P) (g : Fin 4) (x y : Fin 3) : Op :=
  rowCell (pure E g) (fmsInstance P g) E.supportA x y

theorem magicSupport_eq (E : SupportedScaffold P) (g : Fin 4) :
    magicSupport E g=∑ k : Fin 4,parameter E (1+4*g.val+k.val) := by
  have h := BridgeMatrixUnits.units_analysis (pure E g) (fmsInstance P g)
    (pure_laws E g).1 E.densityA (pure_laws E g).2.2 E.supportA E.supportA_laws
  unfold magicSupport
  rw [← h.2.2.2.2]
  apply Finset.sum_congr rfl
  intro i _
  rw [h.2.2.1]
  simpa only [magicA,normalOfPure,(pure_laws E g).2.1] using
    magic_binding P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws g i

theorem cells_pairs (E : SupportedScaffold P) (g : Fin 4) :
    TwoPairs (magicSupport E g) (cell E g 1 1) (cell E g 0 0)
      (cell E g 0 1) (cell E g 1 0) := by
  obtain ⟨h1,h2,hxx,hxz,hzx,hzz⟩ := actual_pauli_pairs (pure E g) (fmsInstance P g)
    (pure_laws E g).1 E.densityA (pure_laws E g).2.2 E.supportA E.supportA_laws
  exact ⟨h1,h2,hxx,hxz,hzx,hzz⟩

theorem target_diagonal (E : SupportedScaffold P) (g : Fin 4) :
    parameter E (1+4*g.val)=diagonal (magicSupport E g) (cell E g 0 0) (cell E g 1 0) (0,0) := by
  have h := DiagonalIdentification.magic_diagonal (pure E g) (fmsInstance P g)
    (pure_laws E g).1 E.densityA (pure_laws E g).2.2 E.supportA E.supportA_laws 0
  have hm := magic_binding P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws g 0
  simp only [Fin.val_zero,Nat.add_zero] at hm
  change E.supportA*magicA E.strategy (fmsInstance P g) 0*E.supportA=parameter E (1+4*g.val) at hm
  rw [← hm]
  simpa [magicSupport,cell,magicA,normalOfPure,(pure_laws E g).2.1] using h.symm


theorem coarse_axis_formula (B : Fin 12 → Op) :
    coarse B (fun a => decide (0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false)) true=B 1+B 3 := by
  norm_num [coarse,cellSign,Fin.sum_univ_succ]


theorem cell_axis_parameter (E : SupportedScaffold P) (g : Fin 4) (k : Fin 2) :
    (2:ℂ) • parameter E (17+2*g.val+k.val)-magicSupport E g=
      cell E g (if k=0 then 1 else 0) 1 := by
  have h := axis_binding P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws g k
    (if k=0 then 1 else 0) (by fin_cases k <;> rfl)
  change _=parameter E (17+2*g.val+k.val) at h
  have hx := coarse_axis_formula (compressed E.supportA (E.strategy.measurements.alice ((fmsInstance P g).qA (if k=0 then 1 else 0))))
  calc
    _=(2:ℂ) • (compressed E.supportA (E.strategy.measurements.alice ((fmsInstance P g).qA (if k=0 then 1 else 0))) 1+
      compressed E.supportA (E.strategy.measurements.alice ((fmsInstance P g).qA (if k=0 then 1 else 0))) 3)-magicSupport E g := by
      exact congrArg (fun X : Op => (2:ℂ) • X-magicSupport E g) (h.symm.trans hx)
    _=_ := by
      change (2:ℂ) • (E.supportA*E.strategy.measurements.alice ((fmsInstance P g).qA (if k=0 then 1 else 0)) ((fmsInstance P g).aA 1)*E.supportA+
        E.supportA*E.strategy.measurements.alice ((fmsInstance P g).qA (if k=0 then 1 else 0)) ((fmsInstance P g).aA 3)*E.supportA)-magicSupport E g=_
      have hm := common_active (pure E g) (fmsInstance P g) (pure_laws E g).1
        E.densityA (pure_laws E g).2.2 E.supportA E.supportA_laws (if k=0 then 1 else 0)
      change rowActive (pure E g) (fmsInstance P g) E.supportA (if k=0 then 1 else 0)=magicSupport E g at hm
      rw [← hm]
      fin_cases k <;>
        norm_num [cell,rowCell,rowActive,rowPOVM,signed,active,coarse,compressed,cellClass,cellSign,
          Fin.sum_univ_succ,scenario,fmsInstance,AA,normalOfPure,(pure_laws E g).2.1] <;> module

theorem value_scale (E : SupportedScaffold P) (q : ℚ) (p : Poly) :
    value E (scale q p)=(q:ℂ) • value E p := by
  simp only [value,evalPoly_scale,smul_mul_assoc]

theorem value_magic (E : SupportedScaffold P) (g : Fin 4) :
    value E (magic g.val)=magicSupport E g*frame E := by
  rw [magic,value_sum,magicSupport_eq]
  have hc (k : Fin 4) : value E (corner (1+4*g.val+k.val))=parameter E (1+4*g.val+k.val)*frame E :=
    eval_corner_frame E ⟨_,by have := g.isLt; have := k.isLt; omega⟩
  norm_num [List.range_succ,Fin.sum_univ_succ]
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2; have h3 := hc 3
  norm_num at h0 h1 h2 h3
  rw [h0,h1,h2,h3]
  noncomm_ring

theorem axis_structural_mem (P : Presentation) (g : Fin 4) (k : Fin 2) :
    sub (axis g.val k.val) (one ++ scale (-2) (magic g.val) ++ scale 2 (axisParameter g.val k.val))
      ∈ structuralPolynomials P := by
  have hm : sub (axis g.val k.val) (one ++ scale (-2) (magic g.val) ++ scale 2 (axisParameter g.val k.val)) ∈
      (List.range 4).flatMap (fun g => (List.range 2).map (fun k =>
        sub (axis g k) (one ++ scale (-2) (magic g) ++ scale 2 (axisParameter g k)))) :=
    List.mem_flatMap.mpr ⟨g.val,List.mem_range.mpr g.isLt,
      List.mem_map.mpr ⟨k.val,List.mem_range.mpr k.isLt,rfl⟩⟩
  simp only [structuralPolynomials,List.mem_append]
  tauto

/-- The two literal numbered axes use the actual extracted Pauli cells. -/
theorem axis_value (E : SupportedScaffold P) (g : Fin 4) (k : Fin 2) :
    value E (axis g.val k.val)=
      frame E-magicSupport E g*frame E+cell E g (if k=0 then 1 else 0) 1*frame E := by
  have hp := structural_equations E _ (axis_structural_mem P g k)
  change value E (sub _ _)=0 at hp
  rw [value_sub] at hp
  rw [sub_eq_zero.mp hp,value_append,value_append,value_one,value_scale,value_scale,value_magic]
  have hc : value E (axisParameter g.val k.val)=parameter E (17+2*g.val+k.val)*frame E :=
    eval_corner_frame E ⟨_,by have := g.isLt; have := k.isLt; omega⟩
  rw [hc,← cell_axis_parameter E g k,sub_mul,smul_mul_assoc]
  norm_num only [Rat.cast_neg,Rat.cast_ofNat]
  module

/-- An anticommuting axis has zero compression to a positive eigencorner. -/
theorem sandwich_anticommute (C Z A : Op) (hCZ : C*Z=C) (hZC : Z*C=C)
    (hZA : Z*A= -(A*Z)) : C*A*C=0 := by
  have he : C*A*C= -(C*A*C) := by
    calc
      _=C*(Z*A)*C := by rw [← mul_assoc,hCZ]
      _= -(C*A*(Z*C)) := by
        rw [hZA]
        simp only [← neg_one_smul ℂ (A*Z),mul_smul_comm,smul_mul_assoc,mul_assoc]
        module
      _= -(C*A*C) := by rw [hZC]
  have htwo : (2:ℂ) • (C*A*C)=0 := by
    calc
      _=C*A*C+C*A*C := by module
      _=0 := eq_neg_iff_add_eq_zero.mp he
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)


theorem projector_eigen (M X Z : Op) (h : Pair M X Z) :
    Z*projector M Z 0=projector M Z 0 ∧ projector M Z 0*Z=projector M Z 0 := by
  constructor <;> norm_num [projector,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,h.Ze,h.eZ,h.ZZ] <;> module

theorem diagonal_eigen (M X Z Y W : Op) (h : TwoPairs M X Z Y W) :
    let C := diagonal M Z W (0,0)
    C*Z=C ∧ Z*C=C ∧ C*W=C ∧ W*C=C := by
  let A := projector M Z 0
  let B := projector M W 0
  have ha := projector_eigen M X Z h.first
  have hb := projector_eigen M Y W h.second
  have hz : Commute Z B := commute_projector Z M W
    (h.first.Ze.trans h.first.eZ.symm) h.ZZ 0
  have hw : Commute W A := commute_projector W M Z
    (h.second.Ze.trans h.second.eZ.symm) h.ZZ.symm 0
  change (A*B)*Z=A*B ∧ Z*(A*B)=A*B ∧ (A*B)*W=A*B ∧ W*(A*B)=A*B
  refine ⟨?_,?_,?_,?_⟩
  · calc
      _=A*(Z*B) := by rw [mul_assoc,← hz.eq]
      _=A*B := by rw [← mul_assoc,ha.2]
  · rw [← mul_assoc,ha.1]
  · rw [mul_assoc,hb.2]
  · calc
      _=(A*W)*B := by rw [← mul_assoc,hw.eq]
      _=A*B := by rw [mul_assoc,hb.1]

/-- All nonidentity axis words vanish when sandwiched by the same chosen
magic corner. The two axes and corner are the literal original ones. -/
theorem target_cell_sandwich (E : SupportedScaffold P) (g : Fin 4) :
    let C := parameter E (1+4*g.val)
    C*cell E g 1 1*C=0 ∧ C*cell E g 0 1*C=0 ∧
      C*(cell E g 1 1*cell E g 0 1)*C=0 := by
  have h := cells_pairs E g
  have he := diagonal_eigen _ _ _ _ _ h
  rw [← target_diagonal E g] at he
  dsimp only at he ⊢
  have hz : cell E g 0 0*cell E g 1 1= -(cell E g 1 1*cell E g 0 0) := by
    rw [h.first.XZ,neg_neg]
  have hw : cell E g 1 0*cell E g 0 1= -(cell E g 0 1*cell E g 1 0) := by
    rw [h.second.XZ,neg_neg]
  refine ⟨sandwich_anticommute _ _ _ he.1 he.2.1 hz,
    sandwich_anticommute _ _ _ he.2.2.1 he.2.2.2 hw,?_⟩
  apply sandwich_anticommute _ _ _ he.1 he.2.1
  calc
    _= -(cell E g 1 1*(cell E g 0 0*cell E g 0 1)) := by
      rw [← mul_assoc,hz]
      simp only [← neg_one_smul ℂ (cell E g 1 1*cell E g 0 0),smul_mul_assoc,mul_assoc]
      module
    _= -(cell E g 1 1*cell E g 0 1*cell E g 0 0) := by rw [h.ZX.eq,mul_assoc]

#print axioms target_cell_sandwich

#print axioms magicSupport_eq
#print axioms cells_pairs
#print axioms target_diagonal
#print axioms cell_axis_parameter
#print axioms axis_value
#print axioms sandwich_anticommute
end Sigma2.CompilerSoundnessAxis
