import Sigma2.CompilerSoundnessIntertwiners

/-! The two literal block sandwiches. -/
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessTransport
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCopies CompilerSoundnessAxis CompilerSoundnessLift
  CompilerSoundnessDictionary CompilerSoundnessAxisCompression CompilerSoundnessBlockCompression
  CompilerSoundnessIntertwiners CompilerSoundnessCover CompilerSoundnessBridgeFrame
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

theorem sandwich_list_sum (C : Op) (xs : List Op) :
    C*xs.sum*C=(xs.map (fun A => C*A*C)).sum := by
  induction xs with
  | nil => simp
  | cons A xs ih => simp only [List.sum_cons,List.map_cons,mul_add,add_mul,ih]

theorem source_transport_zero (E : SupportedScaffold P) (g : Fin 4)
    (l : Fin (encodingCount P)) (k : ℕ) (hk : k<4) :
    corner E g.val*(axisWord E g k*encoded E (g.val+1) l.val*star (axisWord E g k))*corner E g.val=0 := by
  have ht : corner E g.val*axisWord E g k=corner E g.val := (axisWord_source E g ⟨k,hk⟩).1
  calc
    _=(corner E g.val*axisWord E g k)*encoded E (g.val+1) l.val*star (axisWord E g k)*corner E g.val := by simp only [mul_assoc]
    _=0 := by
      rw [ht]
      unfold encoded
      simp only [← mul_assoc,(corners_orthogonal E g).1,zero_mul]

theorem target_transport (E : SupportedScaffold P) (g : Fin 4)
    (l : Fin (encodingCount P)) (k : ℕ) (hk : k<4) :
    corner E (g.val+1)*(axisWord E g k*encoded E (g.val+1) l.val*star (axisWord E g k))*corner E (g.val+1)=
      if k=0 then encoded E (g.val+1) l.val else 0 := by
  have ht : corner E (g.val+1)*axisWord E g k*corner E (g.val+1)=if k=0 then corner E (g.val+1) else 0 := by
    simpa only [CompilerSoundnessIntertwiners.corner,next_index,Fin.ext_iff,Fin.val_zero] using axisWord_target E g ⟨k,hk⟩
  by_cases h0 : k=0
  · subst k
    rw [if_pos rfl,(axisWord_values E g).1,E.supportA_laws.1.1]
    have hr : g.val+1<5 := by have := g.isLt; omega
    have hv := encoded_supported E ⟨g.val+1,hr⟩ l
    calc
      _=(corner E (g.val+1)*E.supportA)*encoded E (g.val+1) l.val*(E.supportA*corner E (g.val+1)) := by simp only [mul_assoc]
      _=encoded E (g.val+1) l.val := by rw [(corner_supported E _).2,(corner_supported E _).1,hv.1,hv.2]
  · rw [if_neg h0] at ht ⊢
    calc
      _=(corner E (g.val+1)*axisWord E g k*corner E (g.val+1))*copy E (g.val+1) l.val*
          star (axisWord E g k)*corner E (g.val+1) := by rfl
      _=0 := by rw [ht,zero_mul,zero_mul,zero_mul]

theorem block_source_sandwich (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    corner E g.val*fullValue E (blockAtom P g.val l.val)*corner E g.val=encoded E g.val l.val := by
  have hr : g.val<5 := by have := g.isLt; omega
  have hvs := encoded_supported E ⟨g.val,hr⟩ l
  have hm : corner E g.val*magicSupport E g=0 := (source_magic_zero E g).1
  have hcomp : corner E g.val*(E.supportA-corner E g.val-magicSupport E g)*corner E g.val=0 := by
    rw [mul_sub,mul_sub,(corner_supported E _).2,(corner_projection E _).2,hm,sub_self,sub_zero,zero_mul]
  have hsum : corner E g.val*((List.range 4).map (fun k => axisWord E g k*encoded E (g.val+1) l.val*star (axisWord E g k))).sum*corner E g.val=0 := by
    rw [sandwich_list_sum,List.map_map]
    apply List.sum_eq_zero
    intro A hA
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hA
    exact source_transport_zero E g l k (List.mem_range.mp hk)
  rw [literal_block,mul_add,mul_add,add_mul,add_mul,hcomp,hsum,hvs.1,hvs.2,zero_add,add_zero]

theorem block_target_sandwich (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    corner E (g.val+1)*fullValue E (blockAtom P g.val l.val)*corner E (g.val+1)=encoded E (g.val+1) l.val := by
  have hm : corner E (g.val+1)*magicSupport E g=corner E (g.val+1) := by
    simpa only [CompilerSoundnessIntertwiners.corner,next_index] using (target_magic E g).2
  have hcomp : corner E (g.val+1)*(E.supportA-corner E g.val-magicSupport E g)*corner E (g.val+1)=0 := by
    rw [mul_sub,mul_sub,(corner_supported E _).2,(corners_orthogonal E g).2,hm,sub_zero,sub_self,zero_mul]
  have hsource : corner E (g.val+1)*encoded E g.val l.val*corner E (g.val+1)=0 := by
    change corner E (g.val+1)*(corner E g.val*copy E g.val l.val)*corner E (g.val+1)=0
    rw [← mul_assoc,(corners_orthogonal E g).2,zero_mul,zero_mul]
  have hsum : corner E (g.val+1)*((List.range 4).map (fun k => axisWord E g k*encoded E (g.val+1) l.val*star (axisWord E g k))).sum*corner E (g.val+1)=encoded E (g.val+1) l.val := by
    rw [sandwich_list_sum,List.map_map]
    have h0 := target_transport E g l 0 (by omega)
    have h1 := target_transport E g l 1 (by omega)
    have h2 := target_transport E g l 2 (by omega)
    have h3 := target_transport E g l 3 (by omega)
    norm_num at h0 h1 h2 h3
    norm_num [List.range_succ]
    rw [h0,h1,h2,h3]
    simp
  rw [literal_block,mul_add,mul_add,add_mul,add_mul,hcomp,hsource,hsum,zero_add,zero_add]

#print axioms block_source_sandwich
#print axioms block_target_sandwich
end Sigma2.CompilerSoundnessTransport
