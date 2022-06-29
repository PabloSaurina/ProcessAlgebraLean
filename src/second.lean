
universes u v

-- mutual inductive css, css_body (α β : Type u) 
-- with css : Type u
-- | proc (nam : α) (bod : css_body) : css
-- | self : css
-- with css_body : Type u
-- | zero : css_body
-- | black : css_body
-- | call (proc : css) : css_body
-- | act (lab : β) (rest : css_body) : css_body
-- | par (proc1 proc2 : css_body): css_body


-- Tengo que encontrar la forma de asignarle un 'nombre' al proceso,
-- igual no hace falta en realidad (probamos con 'self').

-- self === head

inductive css 
| self : css
| zero : css 
| to (other : css) : css
| act (lab:ℕ) (next: css) : css
| proc (pr : css) (next : css) : css
| choice (left: css) (right: css) : css
| par (left: css) (right: css) : css

export css (self zero to act proc choice par)

-- def uno := self
-- def dos := act 2 uno
-- def tres := par zero dos
-- def cuatro := act 1 (act 2 zero)

-- #check uno
-- #check dos
-- #check tres 
-- #check cuatro 

namespace css

instance : decidable_eq css := by tactic.mk_dec_eq_instance

def first_proc : css → set css
|zero := {}
|(to a) := first_proc a
|(act _ _) := {}
|(proc a _) := first_proc a
|(choice a b) := set.union (first_proc a) (first_proc b)
|(par a b) := set.union (first_proc a) (first_proc b)
|self := {self}

def transition_base : css → ℕ → set css 
|(act a b) c := if a = c then first_proc b else {}
|(choice l r) a:= set.union (transition_base l a) (transition_base r a)
|(par l r) a:= set.union (transition_base l a) (transition_base r a)
|_ _ := {}

def transition_no_base : css → css → ℕ → set css
|(proc a b) c n := if a = c then transition_base b n else {}
|(choice a b) c n := if a = c ∧ b = c then set.union (transition_base a n)
  (transition_base b n) else
    if a = c then set.union (transition_base a n) (transition_no_base b c n) 
    else
      if b = c then set.union (transition_base b n) 
      (transition_no_base a c n) else set.union (transition_no_base a c n) 
      (transition_no_base b c n)
|(par a b) c n := if a = c ∧ b = c then set.union (transition_base a n)
  (transition_base b n) else
    if a = c then set.union (transition_base a n) (transition_no_base b c n) 
    else
      if b = c then set.union (transition_base b n) 
      (transition_no_base a c n) else set.union (transition_no_base a c n) 
      (transition_no_base b c n)
|_ _ _ := {}

def transition : css → css → ℕ → set css
|a c n := if a = c then transition_base a n else transition_no_base a c n


-- def strong_bisimulation (r₁: css → css → Prop):= ∀ x y, (∀ a (x₁:proc), 
--   (r₁ x y ∧ P.transition x a = x₁) → ∃ (y₁:proc), (P.transition y a = y₁ 
--   ∧ (r₁ x₁ y₁))) ∧ (∀ b (y₁:proc), (r₁ x y ∧ P.transition y b = y₁) → ∃ 
--   (x₁:proc), (P.transition x b = x₁ ∧ (r₁ x₁ y₁)))

end css