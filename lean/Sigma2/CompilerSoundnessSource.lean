import Sigma2.CompilerSoundnessDecoded
import Sigma2.MatrixSupportDensity
import Sigma2.CornerCompression
import Sigma2.EntropyBridge

/-! The full named source has the required faithful trace-one density.
This uses the full source event, with no qutrit-corner normalization. -/
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessSource
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCover Preliminaries TraceProducts Coefficients
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

def support (E : SupportedScaffold P) : Op :=
  projectionA P E.strategy E.supportA (.parameter 0)

theorem support_projection (E : SupportedScaffold P) : Projection (support E) := E.sharpA _
theorem source_central (E : SupportedScaffold P) : Commute E.densityA.op (support E) :=
  centralA P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws _
theorem source_supported (E : SupportedScaffold P) :
    E.supportA*support E=support E ∧ support E*E.supportA=support E :=
  projectionA_supported P E.strategy E.supportA E.supportA_laws.1 _

attribute [local irreducible] support

theorem source_diagonal (E : SupportedScaffold P) :
    Summable (fun k => entry (E.densityA.op*support E) k k) := by
  have hp : Positive (support E) :=
    ContinuousLinearMap.IsPositive.of_isStarProjection
      ⟨(support_projection E).2,(support_projection E).1⟩
  have hh := covariance_mul_trace (rootFamily E.densityA) (root_summable E.densityA) (support E) hp
  rw [← density_eq_covariance E.densityA] at hh
  exact hh.1

theorem source_trace (E : SupportedScaffold P) :
    (∑' k,(entry (E.densityA.op*support E) k k).re)=1/121 := by
  have hh : (trace (E.densityA.op*support E)).re=1/121 := by
    unfold support
    exact supported_source_mass E
  rw [trace,Complex.re_tsum (source_diagonal E)] at hh
  exact hh

def density (E : SupportedScaffold P) : Density where
  op := (121:ℂ) • (E.densityA.op*support E)
  positive := by
    have he : E.densityA.op*support E=support E*E.densityA.op*star (support E) := by
      rw [(support_projection E).1,← (source_central E).eq,mul_assoc,(support_projection E).2]
    rw [he]
    exact (E.densityA.positive.conj_adjoint (support E)).smul_of_nonneg (by norm_num [Complex.le_def])
  diagonal_summable := by
    have hs := ((source_diagonal E).hasSum.mapL Complex.reCLM).summable
    simpa [entry,Complex.mul_re] using hs.mul_left 121
  trace_one := by
    have hm : (121:ℝ)*(∑' k,(entry (E.densityA.op*support E) k k).re)=1 := by
      rw [source_trace]
      norm_num
    simpa [entry,Complex.mul_re,tsum_mul_left] using hm

/-- Exactly the density formula in the final source-event contract. -/
theorem density_formula (E : SupportedScaffold P) :
    (density E).op=(121:ℂ) • (support E*E.densityA.op*support E) := by
  change (121:ℂ) • (E.densityA.op*support E)=_
  rw [← (source_central E).eq,mul_assoc,(support_projection E).2]

theorem density_support (E : SupportedScaffold P) : SupportOf (density E) (support E) := by
  refine ⟨support_projection E,?_,?_⟩
  · change support E*((121:ℂ) • (E.densityA.op*support E))=_
    rw [mul_smul_comm,← mul_assoc,← (source_central E).eq,mul_assoc,(support_projection E).2]
    rfl
  · intro v hv hz
    apply E.supportA_laws.2.2 v
    · have hh := congrArg (fun A : Op => A v) (source_supported E).1
      change E.supportA (support E v)=support E v at hh
      rwa [hv] at hh
    · change (121:ℂ) • E.densityA.op (support E v)=0 at hz
      rw [hv] at hz
      exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The normalized source is dominated by 121 times the original marginal. -/
theorem density_dominated (E : SupportedScaffold P) :
    Positive (E.densityA.op-(1/121:ℂ) • (density E).op) := by
  have hp := Compiler.projection_compl (support E) (support_projection E)
  have hc : (1-support E)*E.densityA.op=E.densityA.op*(1-support E) := by
    rw [sub_mul,mul_sub,one_mul,mul_one,(source_central E).eq]
  have hpos := CornerCompression.positive (1-support E) hp E.densityA.op hc E.densityA.positive
  have he : E.densityA.op-(1/121:ℂ) • (density E).op=(1-support E)*E.densityA.op := by
    change E.densityA.op-(1/121:ℂ) • ((121:ℂ) • (E.densityA.op*support E))=_
    rw [smul_smul,show (1/121:ℂ)*(121:ℂ)=1 by norm_num,one_smul,
      sub_mul,one_mul,(source_central E).eq]
  rw [he]
  exact hpos

theorem density_finite_entropy (E : SupportedScaffold P)
    (h : FiniteDensityEntropy E.densityA) : FiniteDensityEntropy (density E) := by
  apply EntropySpectrum.finite_entropy_of_dominated E.densityA (density E) (1/121) (by norm_num) _ h
  convert density_dominated E using 1 <;> norm_num

theorem density_finite_of_strategy (E : SupportedScaffold P)
    (h : FiniteMarginalEntropy E.strategy) : FiniteDensityEntropy (density E) := by
  obtain ⟨hA,hB,hmA,hmB,hentA,hentB⟩ := h
  apply density_finite_entropy E
  have hop : E.densityA.op=hA.op :=
    PureSupport.op_ext _ _ (fun i j => (E.marginalA i j).trans (hmA i j).symm)
  obtain ⟨p,u,hp,hs,ht,hu,he,hent⟩ := hentA
  refine ⟨p,u,hp,hs,ht,hu,?_,hent⟩
  simpa only [hop] using he

/-- The normalized source comes from one actual final-game extraction. -/
theorem source_of_final (P : Presentation) (T : NormalStrategy (finalGame P).scenario)
    (hT : Perfect (finalGame P) T) :
    ∃ E : SupportedScaffold P,
      Extends (RowGame.embedding (preGame P) (rows P)) E.strategy T ∧
      SupportOf (density E) (support E) ∧
      (FiniteMarginalEntropy T → FiniteDensityEntropy (density E)) := by
  obtain ⟨E,hExt,hEnt⟩ := of_final P T hT
  exact ⟨E,hExt,density_support E,fun h => density_finite_of_strategy E (hEnt.mpr h)⟩

#print axioms density_finite_of_strategy
#print axioms source_of_final

#print axioms density_dominated
#print axioms density_finite_entropy

#print axioms source_diagonal
#print axioms source_trace
#print axioms density
#print axioms density_formula
#print axioms density_support
end Sigma2.CompilerSoundnessSource
