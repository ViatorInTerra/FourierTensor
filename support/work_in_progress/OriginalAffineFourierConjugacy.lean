import work_in_progress.OriginalQuadraticAdapterWords

/-! Exact affine adapter for a nonalternating quadratic multiplier.
Its native execution consists of two physical affine routes around ONE
canonical kernel batch. The duality and symbol-normal-form certificates
are explicit finite algebraic hypotheses, not a fast execution oracle.
-/
namespace FourierSchur.OriginalAffineFourierConjugacy
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def conjugated (A : CMat α) (e : Space α≃Space α) (k : Space α) : CMat α :=
  fun p q => A (e p) (e q+k)

def conjugatedSymbol (psi : Space α→ℂ) (d : Space α≃Space α) (k : Space α)
    (xi : Space α) : ℂ := psi (d.symm xi)*sign (dot k (d.symm xi))

private theorem dot_add_left (a b c : Space α) : dot (a+b) c=dot a c+dot b c := by
  simp [dot,add_mul,Finset.sum_add_distrib]

/-- Transpose-dual changes of physical/frequency coordinates preserve the
unnormalized Walsh pairing. This is a proof identity, not a runtime call. -/
theorem affine_conjugate_phase (A : CMat α) (psi : Space α→ℂ)
    (hA : A*wal α=wal α*diagonal psi)
    (e d : Space α≃Space α) (hdual : ∀ x y,dot (e x) y=dot x (d y))
    (k : Space α) :
    conjugated A e k*wal α=wal α*diagonal (conjugatedSymbol psi d k) := by
  ext p xi
  let eta := d.symm xi
  have hd : d eta=xi := d.apply_symm_apply xi
  have hwal (q : Space α) :
      wal α q xi=wal α (e q+k) eta*sign (dot k eta) := by
    rw [wal_apply,wal_apply,dot_add_left,sign_add,mul_assoc,sign_sq,mul_one,hdual,hd]
  rw [Matrix.mul_apply,Matrix.mul_diagonal]
  simp only [conjugated]
  have hre : (∑ q,A (e p) (e q+k)*wal α q xi)=
      (∑ q,A (e p) (e q+k)*wal α (e q+k) eta)*sign (dot k eta) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    rw [hwal,mul_assoc]
  rw [hre]
  have hs : (∑ q,A (e p) (e q+k)*wal α (e q+k) eta)=
      ∑ z,A (e p) z*wal α z eta :=
    Equiv.sum_comp (e.trans (Equiv.addRight k)) (fun z => A (e p) z*wal α z eta)
  rw [hs]
  have H := congr_fun (congr_fun hA (e p)) eta
  rw [Matrix.mul_apply,Matrix.mul_diagonal] at H
  rw [H]
  simp only [wal_apply,hdual,hd,conjugatedSymbol]
  ring

theorem affine_conjugate_wrap (A : CMat α) (psi : Space α→ℂ)
    (hA : A*wal α=wal α*diagonal psi)
    (e d : Space α≃Space α) (hdual : ∀ x y,dot (e x) y=dot x (d y))
    (k : Space α) :
    wrap (conjugatedSymbol psi d k)=conjugated A e k :=
  wrap_of _ _ (affine_conjugate_phase A psi hA e d hdual k)

/-- A normal form is certified at q(W*eta), where W is transpose-dual to
the physical address map. Even radical coefficients are retained in k. -/
theorem certified_symbol_adapter (A : CMat α) (psi phi : Space α→ℂ)
    (hA : A*wal α=wal α*diagonal psi)
    (e d : Space α≃Space α) (hdual : ∀ x y,dot (e x) y=dot x (d y))
    (k : Space α)
    (hphi : ∀ eta,phi (d eta)=psi eta*sign (dot k eta)) :
    wrap phi=conjugated A e k := by
  have hp : phi=conjugatedSymbol psi d k := by
    funext xi
    have H := hphi (d.symm xi)
    simpa only [d.apply_symm_apply] using H
  rw [hp]
  exact affine_conjugate_wrap A psi hA e d hdual k

theorem certified_frame_adapter (B : OBase α) (T : Finset α) (phi : Space α→ℂ)
    (e d : Space α≃Space α) (hdual : ∀ x y,dot (e x) y=dot x (d y))
    (k : Space α)
    (hphi : ∀ eta,phi (d eta)=lum (B.proj T eta)*sign (dot k eta)) :
    wrap phi=conjugated (frame B T) e k := by
  apply certified_symbol_adapter _ _ _ _ e d hdual k hphi
  simp [frame,wrap,Matrix.mul_assoc,wal_left]

/-- Literal data-map identity of the two affine passes surrounding the
one common kernel. The inverse route is paid by PhysicalAffineRAM. -/
theorem conjugated_apply (A : CMat α) (e : Space α≃Space α) (k : Space α)
    (x : Space α→ℂ) (p : Space α) :
    (conjugated A e k).mulVec x p=
      A.mulVec (fun z => x (e.symm (z-k))) (e p) := by
  unfold Matrix.mulVec dotProduct conjugated
  have hpoint (q : Space α) :
      A (e p) (e q+k)*x q=A (e p) (e q+k)*x (e.symm ((e q+k)-k)) := by simp
  simp_rw [hpoint]
  exact Equiv.sum_comp (e.trans (Equiv.addRight k))
    (fun z => A (e p) z*x (e.symm (z-k)))

def lifted (f : ℕ) (M : CMat α) : Matrix (Fin f→Space α) (Fin f→Space α) ℂ :=
  digitProd (fun _ => M)

theorem conjugated_apply_amplified (f : ℕ) (A : CMat α)
    (e : Space α≃Space α) (k : Space α) (x : (Fin f→Space α)→ℂ)
    (p : Fin f→Space α) :
    (lifted f (conjugated A e k)).mulVec x p=
      (lifted f A).mulVec (fun z => x (fun j => e.symm (z j-k)))
        (fun j => e (p j)) := by
  let E : (Fin f→Space α)≃(Fin f→Space α) :=
    { toFun := fun y j => e (y j)+k
      invFun := fun z j => e.symm (z j-k)
      left_inv := by intro y; funext j; simp
      right_inv := by intro z; funext j; simp }
  unfold Matrix.mulVec dotProduct lifted
  simp only [digitProd_apply,conjugated]
  simpa [E] using Equiv.sum_comp E
    (fun z => (∏ j,A (e (p j)) (z j))*x (fun j => e.symm (z j-k)))

/-- Equality of the whole tensor map for every amplification, on arbitrary
independent complex inputs. No f-dependent phase is inferred from f=1. -/
theorem certified_symbol_adapter_amplified (f : ℕ) (A : CMat α)
    (psi phi : Space α→ℂ) (hA : A*wal α=wal α*diagonal psi)
    (e d : Space α≃Space α) (hdual : ∀ x y,dot (e x) y=dot x (d y))
    (k : Space α) (hphi : ∀ eta,phi (d eta)=psi eta*sign (dot k eta)) :
    lifted f (wrap phi)=lifted f (conjugated A e k) := by
  rw [certified_symbol_adapter A psi phi hA e d hdual k hphi]

section NativeWord
variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-- Literal semantics of the actual three-token word, for all f. The two
matrix/address identities are finite affine certificates for that word. -/
theorem affine_adapter_selected (A : ρ→OBase α) (f : ℕ) (x : Data α ρ f)
    (l : ρ) (T : Finset α) (e : Space α≃Space α) (k : Space α)
    (Mright Mleft : Matrix α α F) (zright : Space α)
    (hleft : ∀ p,OriginalPhysicalAffineRAM.affine Mleft 0 p=e p)
    (hright : ∀ z,OriginalPhysicalAffineRAM.affine Mright zright z=e.symm (z-k)) :
    OriginalQuadraticAdapterWords.walk A f
      (OriginalQuadraticAdapterWords.affineAdapterWord l T Mright Mleft zright) x l=
      (lifted f (conjugated (frame (A l) T) e k)).mulVec (x l) := by
  funext q
  rw [conjugated_apply_amplified]
  simp [OriginalQuadraticAdapterWords.walk,OriginalQuadraticAdapterWords.affineAdapterWord,
    OriginalQuadraticAdapterWords.Step.go,OriginalContextualChirpWords.Step.go,
    OriginalGroupedFrameWords.Move.go,OriginalQuadraticAdapterWords.soloSubset,
    multiAct,unframe,OBase.proj,wrap_one,hleft,hright,matAct,lifted]

/-- Symbol normal form plus the actual paid native word. Other original
roles are preserved by affine_adapter_off in the word compiler module. -/
theorem certified_native_adapter_selected (A : ρ→OBase α) (f : ℕ)
    (x : Data α ρ f) (l : ρ) (T : Finset α) (phi : Space α→ℂ)
    (e d : Space α≃Space α) (hdual : ∀ x y,dot (e x) y=dot x (d y))
    (k : Space α) (hphi : ∀ eta,phi (d eta)=lum ((A l).proj T eta)*sign (dot k eta))
    (Mright Mleft : Matrix α α F) (zright : Space α)
    (hleft : ∀ p,OriginalPhysicalAffineRAM.affine Mleft 0 p=e p)
    (hright : ∀ z,OriginalPhysicalAffineRAM.affine Mright zright z=e.symm (z-k)) :
    OriginalQuadraticAdapterWords.walk A f
      (OriginalQuadraticAdapterWords.affineAdapterWord l T Mright Mleft zright) x l=
      (lifted f (wrap phi)).mulVec (x l) := by
  rw [certified_frame_adapter (A l) T phi e d hdual k hphi]
  exact affine_adapter_selected A f x l T e k Mright Mleft zright hleft hright
end NativeWord

end
end FourierSchur.OriginalAffineFourierConjugacy
