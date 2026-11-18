import MyProject.ConstantPreparation

/-! Typed composition of preparation DAGs, with exact operation counts and
nonzero-denominator certificates. Existing registers remain available. -/
namespace FourierSchur.ConstantPreparation
noncomputable section

def rename {α β γ : Type} (f : α → γ) : Tape α β → Tape γ β
  | .done o => .done (f ∘ o)
  | .rational q rest => .rational q (rename (Option.map f) rest)
  | .add a b rest => .add (f a) (f b) (rename (Option.map f) rest)
  | .mul a b rest => .mul (f a) (f b) (rename (Option.map f) rest)
  | .inv a rest => .inv (f a) (rename (Option.map f) rest)

theorem extend_map {α γ : Type} (f : α → γ) (x : γ → ℂ) (v : ℂ) :
    extend x v ∘ Option.map f=extend (x ∘ f) v := by
  funext i
  cases i <;> rfl

theorem rename_correct {α β γ : Type} (f : α → γ) (p : Tape α β) (x : γ → ℂ) :
    run (rename f p) x=run p (x ∘ f) := by
  induction p generalizing γ with
  | done o => rfl
  | rational q rest ih => simp only [rename,run]; rw [ih,extend_map]
  | add a b rest ih => simp only [rename,run]; rw [ih,extend_map]; rfl
  | mul a b rest ih => simp only [rename,run]; rw [ih,extend_map]; rfl
  | inv a rest ih => simp only [rename,run]; rw [ih,extend_map]; rfl

theorem rename_operations {α β γ : Type} (f : α → γ) (p : Tape α β) :
    operations (rename f p)=operations p := by
  induction p generalizing γ <;> simp [rename,operations, *]

theorem rename_safe {α β γ : Type} (f : α → γ) (p : Tape α β) (x : γ → ℂ) :
    DenominatorsNonzero (rename f p) x ↔ DenominatorsNonzero p (x ∘ f) := by
  induction p generalizing γ with
  | done o => rfl
  | rational q rest ih => simp only [rename,DenominatorsNonzero]; rw [ih,extend_map]
  | add a b rest ih => simp only [rename,DenominatorsNonzero]; rw [ih,extend_map]; rfl
  | mul a b rest ih => simp only [rename,DenominatorsNonzero]; rw [ih,extend_map]; rfl
  | inv a rest ih => simp only [rename,DenominatorsNonzero]; rw [ih,extend_map]; rfl

def compose {α β γ : Type} : Tape α β → Tape β γ → Tape α γ
  | .done o,q => rename o q
  | .rational r rest,q => .rational r (compose rest q)
  | .add a b rest,q => .add a b (compose rest q)
  | .mul a b rest,q => .mul a b (compose rest q)
  | .inv a rest,q => .inv a (compose rest q)

theorem compose_correct {α β γ : Type} (p : Tape α β) (q : Tape β γ) (x : α → ℂ) :
    run (compose p q) x=run q (run p x) := by
  induction p with
  | done o => exact rename_correct o q x
  | rational r rest ih => exact ih q (extend x r)
  | add a b rest ih => exact ih q (extend x (x a+x b))
  | mul a b rest ih => exact ih q (extend x (x a*x b))
  | inv a rest ih => exact ih q (extend x (x a)⁻¹)

theorem compose_operations {α β γ : Type} (p : Tape α β) (q : Tape β γ) :
    operations (compose p q)=operations p+operations q := by
  induction p <;> simp [compose,operations,rename_operations, *,Nat.add_assoc]

theorem compose_safe {α β γ : Type} (p : Tape α β) (q : Tape β γ) (x : α → ℂ) :
    DenominatorsNonzero (compose p q) x ↔
      DenominatorsNonzero p x ∧ DenominatorsNonzero q (run p x) := by
  induction p with
  | done o => simp [compose,rename_safe,DenominatorsNonzero,run]
  | rational r rest ih => exact ih q (extend x r)
  | add a b rest ih => exact ih q (extend x (x a+x b))
  | mul a b rest ih => exact ih q (extend x (x a*x b))
  | inv a rest ih => simp only [compose,DenominatorsNonzero,run,ih,and_assoc]

def keep {α β γ : Type} (f : γ → α) : Tape α β → Tape α (Sum γ β)
  | .done o => .done (Sum.elim f o)
  | .rational q rest => .rational q (keep (Option.some ∘ f) rest)
  | .add a b rest => .add a b (keep (Option.some ∘ f) rest)
  | .mul a b rest => .mul a b (keep (Option.some ∘ f) rest)
  | .inv a rest => .inv a (keep (Option.some ∘ f) rest)

theorem keep_correct {α β γ : Type} (f : γ → α) (p : Tape α β) (x : α → ℂ) :
    run (keep f p) x=Sum.elim (x ∘ f) (run p x) := by
  induction p with
  | done o => funext i; cases i <;> rfl
  | rational q rest ih => simp only [keep,run]; rw [ih]; rfl
  | add a b rest ih => simp only [keep,run]; rw [ih]; rfl
  | mul a b rest ih => simp only [keep,run]; rw [ih]; rfl
  | inv a rest ih => simp only [keep,run]; rw [ih]; rfl

theorem keep_operations {α β γ : Type} (f : γ → α) (p : Tape α β) :
    operations (keep f p)=operations p := by
  induction p <;> simp [keep,operations, *]

theorem keep_safe {α β γ : Type} (f : γ → α) (p : Tape α β) (x : α → ℂ) :
    DenominatorsNonzero (keep f p) x ↔ DenominatorsNonzero p x := by
  induction p <;> simp [keep,DenominatorsNonzero, *]

def parallel {α β γ δ : Type} (p : Tape α β) (q : Tape γ δ) :
    Tape (Sum α γ) (Sum β δ) :=
  compose (keep id (rename Sum.inl p))
    (keep Sum.inr (rename (Sum.inl ∘ Sum.inr) q))

theorem parallel_correct {α β γ δ : Type} (p : Tape α β) (q : Tape γ δ)
    (x : Sum α γ → ℂ) :
    run (parallel p q) x=Sum.elim (run p (x ∘ Sum.inl)) (run q (x ∘ Sum.inr)) := by
  simp only [parallel,compose_correct,keep_correct,rename_correct]
  rfl

theorem parallel_operations {α β γ δ : Type} (p : Tape α β) (q : Tape γ δ) :
    operations (parallel p q)=operations p+operations q := by
  simp [parallel,compose_operations,keep_operations,rename_operations]

theorem parallel_safe {α β γ δ : Type} (p : Tape α β) (q : Tape γ δ)
    (x : Sum α γ → ℂ) :
    DenominatorsNonzero (parallel p q) x ↔
      DenominatorsNonzero p (x ∘ Sum.inl) ∧ DenominatorsNonzero q (x ∘ Sum.inr) := by
  simp only [parallel,compose_safe,keep_safe,rename_safe,keep_correct,rename_correct]
  rfl

end
end FourierSchur.ConstantPreparation
