import work_in_progress.OriginalNativeGeneratorSymbols

/-! Computable sparse rows and a sound finite certificate checker for the
native bank DAG. Row normalization is exact rational arithmetic. It does
not execute or assume a Fourier transform on the arbitrary complex data.
-/
namespace FourierSchur.OriginalSparseNativeRows
open OAI.PowerSaving OAI.PowerSaving.Binary Matrix Finset
open OriginalNativeGeneratorSymbols
noncomputable section

structure Term where
  input : ℕ
  phase : Tag
  coeff : ℚ
  deriving DecidableEq, Repr

abbrev Row := List Term

def insertTerm (t : Term) : Row → Row
  | [] => if t.coeff=0 then [] else [t]
  | u::us => if t.coeff=0 then u::us else
      if t.input=u.input ∧ t.phase=u.phase then
        if t.coeff+u.coeff=0 then us else {t with coeff:=t.coeff+u.coeff}::us
      else u::insertTerm t us

def normalize : Row → Row
  | [] => []
  | t::ts => insertTerm t (normalize ts)

def mean (F : ℕ → Tag → ℂ) (row : Row) : ℂ :=
  (row.map (fun t => (t.coeff:ℂ)*F t.input t.phase)).sum

theorem mean_cons (F : ℕ → Tag → ℂ) (t : Term) (row : Row) :
    mean F (t::row)=(t.coeff:ℂ)*F t.input t.phase+mean F row := rfl

theorem mean_insertTerm (F : ℕ → Tag → ℂ) (t : Term) (row : Row) :
    mean F (insertTerm t row)=(t.coeff:ℂ)*F t.input t.phase+mean F row := by
  induction row with
  | nil => by_cases h : t.coeff=0 <;> simp [insertTerm,mean,h]
  | cons u us ih =>
    by_cases h0 : t.coeff=0
    · simp [insertTerm,mean,h0]
    · simp only [insertTerm,if_neg h0]
      by_cases hkey : t.input=u.input ∧ t.phase=u.phase
      · rw [if_pos hkey]
        rcases hkey with ⟨hi,hp⟩
        by_cases hc : t.coeff+u.coeff=0
        · have hz : (t.coeff:ℂ)+(u.coeff:ℂ)=0 := by exact_mod_cast hc
          simp only [hi,hp,if_pos hc,mean_cons]
          linear_combination -(F u.input u.phase)*hz
        · simp only [hi,hp,if_neg hc,mean_cons,Rat.cast_add]
          ring
      · rw [if_neg hkey,mean_cons,ih,mean_cons]
        ring

theorem mean_normalize (F : ℕ → Tag → ℂ) (row : Row) :
    mean F (normalize row)=mean F row := by
  induction row with
  | nil => rfl
  | cons t ts ih => rw [normalize,mean_insertTerm,ih,mean_cons]

def scale (c : ℚ) (row : Row) : Row := row.map (fun t => {t with coeff:=c*t.coeff})

theorem mean_scale (F : ℕ → Tag → ℂ) (c : ℚ) (row : Row) :
    mean F (scale c row)=(c:ℂ)*mean F row := by
  induction row with
  | nil => simp [scale,mean]
  | cons t ts ih => simp [scale,mean,Rat.cast_mul] at *; rw [ih]; ring

theorem mean_append (F : ℕ → Tag → ℂ) (a b : Row) :
    mean F (a++b)=mean F a+mean F b := by simp [mean]

def gather (table : ℕ → Row) (inputs : List (ℕ×ℚ)) : Row :=
  inputs.flatMap (fun p => scale p.2 (table p.1))

theorem mean_gather (F : ℕ → Tag → ℂ) (table : ℕ → Row) (inputs : List (ℕ×ℚ)) :
    mean F (gather table inputs)=
      (inputs.map (fun p => (p.2:ℂ)*mean F (table p.1))).sum := by
  induction inputs with
  | nil => rfl
  | cons p ps ih =>
    change mean F (scale p.2 (table p.1)++gather table ps)=_
    rw [mean_append,mean_scale,ih]
    rfl

def phaseMap {k : ℕ} (directions : Fin k → ℕ) (a : Tag) (row : Row) : Row :=
  row.map (fun t => {t with phase:=compose directions a t.phase})

def nextRow {k : ℕ} (directions : Fin k → ℕ) (a : Tag)
    (table : ℕ → Row) (inputs : List (ℕ×ℚ)) : Row :=
  normalize (phaseMap directions a (gather table inputs))

def act {n k : ℕ} (generators : Fin k → Space (Fin n) → ℂ) (f : ℕ)
    (x : ℕ → Sky (Fin n) f → ℂ) (row : Row) : Sky (Fin n) f → ℂ :=
  fun q => mean (fun i t => matAct f (operator generators t) (x i) q) row

theorem matAct_add {n : ℕ} (f : ℕ) (M : CMat (Fin n))
    (x y : Sky (Fin n) f → ℂ) :
    matAct f M (fun q => x q+y q)=fun q => matAct f M x q+matAct f M y q := by
  exact Matrix.mulVec_add _ _ _

theorem matAct_const_mul {n : ℕ} (f : ℕ) (M : CMat (Fin n))
    (c : ℂ) (x : Sky (Fin n) f → ℂ) :
    matAct f M (fun q => c*x q)=fun q => c*matAct f M x q := by
  change (digitProd (fun _ : Fin f => M)).mulVec (c • x)=
    c • (digitProd (fun _ : Fin f => M)).mulVec x
  exact Matrix.mulVec_smul _ _ _

theorem act_phaseMap {n k : ℕ} (directions : Fin k → ℕ)
    (generators : Fin k → Space (Fin n) → ℂ)
    (hs : ∀ i x,generators i x*generators i x=character n (directions i) x)
    (f : ℕ) (x : ℕ → Sky (Fin n) f → ℂ) (a : Tag) (row : Row) :
    act generators f x (phaseMap directions a row)=
      matAct f (operator generators a) (act generators f x row) := by
  induction row with
  | nil =>
    change (fun _ => (0:ℂ))=matAct f (operator generators a) (fun _ => (0:ℂ))
    change (0 : Sky (Fin n) f → ℂ)=(digitProd (fun _ : Fin f => operator generators a)).mulVec 0
    exact (Matrix.mulVec_zero _).symm
  | cons t ts ih =>
    have hr : act generators f x (t::ts)=fun q =>
        (t.coeff:ℂ)*matAct f (operator generators t.phase) (x t.input) q+
          act generators f x ts q := rfl
    rw [hr,matAct_add,matAct_const_mul,matAct_mul]
    funext q
    change (t.coeff:ℂ)*matAct f (operator generators (compose directions a t.phase))
      (x t.input) q+act generators f x (phaseMap directions a ts) q=_
    rw [operator_compose directions generators hs,congr_fun ih q]

theorem act_normalize {n k : ℕ} (generators : Fin k → Space (Fin n) → ℂ)
    (f : ℕ) (x : ℕ → Sky (Fin n) f → ℂ) (row : Row) :
    act generators f x (normalize row)=act generators f x row := by
  funext q
  exact mean_normalize _ row

theorem act_gather {n k : ℕ} (generators : Fin k → Space (Fin n) → ℂ)
    (f : ℕ) (x : ℕ → Sky (Fin n) f → ℂ) (table : ℕ → Row)
    (inputs : List (ℕ×ℚ)) :
    act generators f x (gather table inputs)=fun q =>
      (inputs.map (fun p => (p.2:ℂ)*act generators f x (table p.1) q)).sum := by
  funext q
  exact mean_gather _ table inputs

theorem act_nextRow {n k : ℕ} (directions : Fin k → ℕ)
    (generators : Fin k → Space (Fin n) → ℂ)
    (hs : ∀ i x,generators i x*generators i x=character n (directions i) x)
    (f : ℕ) (x : ℕ → Sky (Fin n) f → ℂ) (a : Tag)
    (table : ℕ → Row) (inputs : List (ℕ×ℚ)) :
    act generators f x (nextRow directions a table inputs)=
      matAct f (operator generators a) (fun q =>
        (inputs.map (fun p => (p.2:ℂ)*act generators f x (table p.1) q)).sum) := by
  rw [nextRow,act_normalize,act_phaseMap directions generators hs,act_gather]

end
end FourierSchur.OriginalSparseNativeRows
