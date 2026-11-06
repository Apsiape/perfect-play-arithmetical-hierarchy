import Sigma2.CompilerSoundnessBridgeCopies

/-! Isometry and modular calibration for the unchanged four-bridge chain. -/
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessChain
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCopies CompilerSoundnessLift CompilerSoundnessDictionary
  CompilerSoundnessIntertwiners CompilerSoundnessBridgeCopies CompilerSoundnessBridgeFrame
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

structure Partial (f g w : Op) : Prop where
  initial : star w*w=f
  final : w*star w=g
  left : g*w=w
  right : w*f=w

theorem compose {f g h w v : Op} (hw : Partial f g w) (hv : Partial g h v) :
    Partial f h (v*w) := by
  constructor
  · rw [star_mul]
    calc
      _=star w*(star v*v)*w := by simp only [mul_assoc]
      _=f := by rw [hv.initial,mul_assoc,hw.left,hw.initial]
  · rw [star_mul]
    calc
      _=v*(w*star w)*star v := by simp only [mul_assoc]
      _=h := by rw [hw.final,hv.right,hv.final]
  · rw [← mul_assoc,hv.left]
  · rw [mul_assoc,hw.right]

theorem bridge_calibration (E : SupportedScaffold P) (g : Fin 4) :
    star (bridge E g)*bridge E g=corner E g.val ∧
      bridge E g*star (bridge E g)=corner E (g.val+1) ∧
      E.densityA.op*bridge E g=(2:ℂ) • (bridge E g*E.densityA.op) := by
  obtain ⟨_,_,_,_,_,_,_,_,h0,h1,hm⟩ := CompilerSoundnessFrame.named_calibration P E.strategy E.perfect
    E.densityA E.marginalA E.supportA E.supportA_laws g
  simpa only [bridge,CompilerSoundnessIntertwiners.corner,next_index,parameter] using And.intro h0 (And.intro h1 hm)

theorem bridge_partial (E : SupportedScaffold P) (g : Fin 4) :
    Partial (corner E g.val) (corner E (g.val+1)) (bridge E g) :=
  ⟨(bridge_calibration E g).1,(bridge_calibration E g).2.1,
    (bridge_corner_support E g).1,(bridge_corner_support E g).2⟩

theorem chain_partial (E : SupportedScaffold P) : Partial (corner E 0) (corner E 4) (chain E) := by
  have h23 : Partial (corner E 2) (corner E 4) (bridge E 3*bridge E 2) :=
    compose (bridge_partial E 2) (bridge_partial E 3)
  have h123 : Partial (corner E 1) (corner E 4) (bridge E 3*bridge E 2*bridge E 1) :=
    compose (bridge_partial E 1) h23
  exact compose (bridge_partial E 0) h123

theorem modular_mul (H A B : Op) (a b : ℂ) (hA : H*A=a • (A*H))
    (hB : H*B=b • (B*H)) : H*(A*B)=(a*b) • (A*B*H) := by
  rw [← mul_assoc,hA,smul_mul_assoc,mul_assoc,hB,mul_smul_comm,smul_smul]
  simp only [mul_assoc]

theorem chain_modular (E : SupportedScaffold P) :
    E.densityA.op*chain E=(16:ℂ) • (chain E*E.densityA.op) := by
  have h23 : E.densityA.op*(bridge E 3*bridge E 2)=(4:ℂ) • ((bridge E 3*bridge E 2)*E.densityA.op) := by
    convert modular_mul _ _ _ _ _ (bridge_calibration E 3).2.2 (bridge_calibration E 2).2.2 using 1 <;> norm_num
  have h123 : E.densityA.op*(bridge E 3*bridge E 2*bridge E 1)=(8:ℂ) • ((bridge E 3*bridge E 2*bridge E 1)*E.densityA.op) := by
    convert modular_mul _ _ _ _ _ h23 (bridge_calibration E 1).2.2 using 1 <;> norm_num
  convert modular_mul _ _ _ _ _ h123 (bridge_calibration E 0).2.2 using 1 <;> norm_num [chain]

theorem chain_adjoint_modular (E : SupportedScaffold P) :
    E.densityA.op*star (chain E)=(1/16:ℂ) • (star (chain E)*E.densityA.op) := by
  have hH : star E.densityA.op=E.densityA.op := E.densityA.positive.isSelfAdjoint
  have hs : star (chain E)*E.densityA.op=(16:ℂ) • (E.densityA.op*star (chain E)) := by
    simpa only [star_mul,hH,PauliMatrixUnits.op_star_smul,star_ofNat] using
      congrArg (fun A : Op => star A) (chain_modular E)
  calc
    _=(1/16:ℂ) • ((16:ℂ) • (E.densityA.op*star (chain E))) := by module
    _=_ := congrArg (fun A : Op => (1/16:ℂ) • A) hs.symm

#print axioms bridge_calibration
#print axioms chain_partial
#print axioms chain_modular
#print axioms chain_adjoint_modular
end Sigma2.CompilerSoundnessChain
