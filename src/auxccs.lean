import data.fintype.basic
import tactic


universe u

inductive aux_ccs (label : Type u)
|zer : aux_ccs
|ap (a : label) (p : aux_ccs): aux_ccs
|pq (p q : aux_ccs) : aux_ccs -- Paralelo
|psq (p : aux_ccs) (q : aux_ccs): aux_ccs -- Suma

export aux_ccs (zer ap pq psq)


namespace aux_ccs

-- Esta solucion no parece muy apropiada pero funciona.
-- El objetivo es 'definir' que pq a b = pq b a, no se hacerlo de otro modo.

-- axiom prop1 (a:aux_ccs act) (b:aux_ccs act): (pq a b) = (pq b a)
-- axiom prop2 (a:aux_ccs act) (b:aux_ccs act): (psq a b) = (psq b a)


-- Esto era de prueba (se puede borrar)

-- def is_equal: aux_ccs → aux_ccs → Prop
-- |zer zer := tt
-- |(ap a p) (ap b q) := (a = b) ∧ is_equal p q 
-- |(pq p q) (pq p₁ q₁) := (is_equal p p₁ ∧ is_equal q q₁) ∨ (is_equal p q₁ ∧ is_equal q p₁)
-- |(psq p q) (psq p₁ q₁) := (is_equal p p₁ ∧ is_equal q q₁) ∨ (is_equal p q₁ ∧ is_equal q p₁) 
-- |_ _ := ff

-- def is_equal_refl_trans_gen : aux_ccs → aux_ccs → Prop :=
-- relation.refl_trans_gen (λ a b, is_equal a b)


-- Definir las igualdades

variables {act : Type u} [decidable_eq act]

instance : decidable_eq (aux_ccs act)
  |zer zer := is_true rfl
  |(ap a p) (ap b q) := if h: a = b then 
    match decidable_eq p q with 
    | is_true peqq := is_true (h ▸ peqq ▸ eq.refl (ap a p))
    | is_false pneq := is_false (λ contra, aux_ccs.no_confusion contra (λ a b, absurd b pneq))
    end
    else is_false (λ contra, aux_ccs.no_confusion contra (λ a b, absurd a h))
  |(pq p₁ q₁) (pq p₂ q₂) := 
    match decidable_eq p₁ p₂ with
    | is_true pep :=
      match decidable_eq q₁ q₂ with
      | is_true qeq := is_true (pep ▸ qeq ▸ eq.refl (pq p₁ q₁))
      | is_false qnq := is_false (λ contra, aux_ccs.no_confusion contra (λ a b, absurd b qnq))
      end
    | is_false pnp := 
      -- match decidable_eq p₁ q₂ with
      -- | is_true peq :=
      --   match decidable_eq q₁ p₂ with
      --   | is_true qep := is_true (peq ▸ qep ▸ prop1 p₁ q₁)
      --   | is_false qnp := is_false(λ contra, aux_ccs.no_confusion contra (λ a b, absurd a pnp))
      --   end
      -- | is_false pnq := is_false(λ contra, aux_ccs.no_confusion contra (λ a b, absurd a pnp))
      -- end
      is_false(λ contra, aux_ccs.no_confusion contra (λ a b, absurd a pnp))
    end
  |(psq p₁ q₁) (psq p₂ q₂) := 
    match decidable_eq p₁ p₂ with
    | is_true pep :=
      match decidable_eq q₁ q₂ with
      | is_true qeq := is_true (pep ▸ qeq ▸ eq.refl (psq p₁ q₁))
      | is_false qnq := is_false (λ contra, aux_ccs.no_confusion contra (λ a b, absurd b qnq))
      end
    | is_false pnp := 
      -- match decidable_eq p₁ q₂ with
      -- | is_true peq :=
      --   match decidable_eq q₁ p₂ with
      --   | is_true qep := is_true (peq ▸ qep ▸ prop2 p₁ q₁)
      --   | is_false qnp := is_false(λ contra, aux_ccs.no_confusion contra (λ a b, absurd a pnp))
      --   end
      -- | is_false pnq := is_false(λ contra, aux_ccs.no_confusion contra (λ a b, absurd a pnp))
      -- end
      is_false(λ contra, aux_ccs.no_confusion contra (λ a b, absurd a pnp))
    end
  |zer (ap a p) := is_false (λ contra, aux_ccs.no_confusion contra)
  |zer (pq p q) := is_false (λ contra, aux_ccs.no_confusion contra)
  |zer (psq p q) := is_false (λ contra, aux_ccs.no_confusion contra)
  |(ap a p) zer := is_false (λ contra, aux_ccs.no_confusion contra)
  |(ap a p) (pq q f) := is_false (λ contra, aux_ccs.no_confusion contra)
  |(ap a p) (psq q f) := is_false (λ contra, aux_ccs.no_confusion contra)
  |(pq q f) zer := is_false (λ contra, aux_ccs.no_confusion contra)
  |(pq q f) (ap a p) := is_false (λ contra, aux_ccs.no_confusion contra)
  |(pq q f) (psq p g) := is_false (λ contra, aux_ccs.no_confusion contra)
  |(psq q f) zer := is_false (λ contra, aux_ccs.no_confusion contra)
  |(psq q f) (ap a p) := is_false (λ contra, aux_ccs.no_confusion contra)
  |(psq q f) (pq p g) := is_false (λ contra, aux_ccs.no_confusion contra)

-- nat.decidable_eq
-- pos.decidable_eq

-- Definimos los símbolos usuales para aux_ccs + . y |


def add : aux_ccs act → aux_ccs act → aux_ccs act
|a b := psq a b

def par : aux_ccs act → aux_ccs act → aux_ccs act
|a b := pq a b

def lab_tran : act → aux_ccs act → aux_ccs act
|a b := ap a b

infix ` + `:50 := aux_ccs.add
infix ` ∣ `:50 := aux_ccs.par
infix ` . `:50 := aux_ccs.lab_tran 

#eval decidable.to_bool (1 . zer + zer = zer)
#check (zer ∣ zer : aux_ccs act)
#check 1 . zer
#eval decidable.to_bool (3 . ((1 . zer) ∣ zer) + zer = (psq (ap 3 (pq (ap 1 zer) zer)) zer))


-- Probamos como hacer la recursión

def fun1 (lab : act) (x : aux_ccs act) : aux_ccs act :=
lab . x

def fun2 (y : aux_ccs act) (x : aux_ccs act) : aux_ccs act :=
y ∣ x

def fun3 (y : aux_ccs act) (x : aux_ccs act) : aux_ccs act :=
y + x

#eval decidable.to_bool (fun1 1 zer = ap 1 zer)
#eval decidable.to_bool (fun2 (fun1 1 zer) zer = pq (ap 1 zer) zer)
#eval decidable.to_bool (fun3 (fun1 1 zer) zer = psq (ap 1 zer) zer)

#check fun2 zer


-- Decidible aux_ccs(x) = aux_ccs(y)

lemma lem1 {f g : aux_ccs act → aux_ccs act}: f = g ↔ (∀ x, f x = g x) :=
iff.intro (assume h a, h ▸ rfl) funext

lemma lem2 {f g : aux_ccs act → aux_ccs act}: (∀ x, f x = g x) → f = g :=
begin
  ext1,
end


-- Esta mal, lo que hay que hacer es definir un tipo x o algo que nos permita
-- asegurar que si f y g son del tipo x, entonces se cumpla el lem3

lemma lem3 {f g : aux_ccs act → aux_ccs act}: f zer = g zer → f = g := sorry

lemma lem4 {f g : aux_ccs act → aux_ccs act}: ¬ f zer = g zer → ¬ f = g := sorry

instance : decidable_eq (aux_ccs act → aux_ccs act)
| f g := if h: f zer = g zer then is_true (lem3 h) else is_false (lem4 h)

end aux_ccs 


-- Strong bisimulation

-- Rest of the properties

-- Ejemplo:
--  definir como hacerlo recursivo


inductive natural
|zero : natural
|sucesor (n : natural) : natural

open classical

example: ∀ p q r, ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
begin
  introv,
  apply iff.intro,
  {
    assume hpqr,
    split,
    {
      assume hp,
      apply hpqr,
      left,
      exact hp,
    },
    {
      assume hq,
      apply hpqr,
      right,
      exact hq,
    },
  },
  {
    assume hprqr,
    cases hprqr,
    assume hpq,
    cases hpq,
    {
      apply hprqr_left,
      exact hpq,
    },
    {
      apply hprqr_right,
      exact hpq,
    },
  },
end
