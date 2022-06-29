import data.fintype.basic
import set_theory.cardinal
import lts
import tactic

universe u 

inductive ccs (lab : Type u)
|zer : ccs
|ap (a:lab) (u:ccs) : ccs
|pq (p:ccs) (q:ccs) : ccs
|psq (p:ccs) (q:ccs) : ccs
|re : ccs
|named (n : ccs): ccs

export ccs (zer ap pq psq re named)


namespace ccs

variables {lab : Type u} [decidable_eq lab]


def sust: ccs lab → ccs lab → ccs lab
|zer n:= zer
|(ap a u) n := (ap a (sust u n))
|(pq p q) n := (pq (sust p n) (sust q n))
|(psq p q) n := (psq (sust p n) (sust q n))
|re n := named n
|(named n) m := named n

def simp: ccs lab → ccs lab
|(named n) := n
|a := a

def sust_simp: ccs lab → ccs lab → ccs lab
|u n := simp (sust u n)

def combinaciones (A B : set (ccs lab)) (a b : ccs lab): set (ccs lab)
|(pq (named c) (named d)) := (c ∈ A ∧ d ∈ B) ∨ (c ∈ A ∧ d = b) ∨ (c = a ∧ b ∈ B)
|p := ff

def utransition : ccs lab → ccs lab → lab → set (ccs lab) 
|n zer a := {}
|n (ap a (psq p q)) b := if a = b then {sust_simp p n,sust_simp q n,sust_simp (psq p q) n} else {}
|n (ap a (pq p q)) b := if a = b then {sust_simp (pq p q) n} else {}
|n (ap a u) b := if a = b then {sust_simp u n} else {}
|n (pq p q) a := combinaciones (utransition n p a) (utransition n q a) 
  (sust_simp p n) (sust_simp q n)
|n (psq p q) a := set.union (utransition n p a) (utransition n q a)
|n (re) a := {}
|n (named m) a := {}

def rest_utransition : ccs lab → ccs lab → lab → set (ccs lab)
|n zer a := {}
|n (ap a u) b := {}
|n (pq p q) a := combinaciones (rest_utransition n p a) (rest_utransition n q a) 
  (sust_simp p n) (sust_simp q n)
|n (psq p q) a := set.union (rest_utransition n p a) (rest_utransition n q a)
|n re a := {}
|n (named m) a := {m}

def map_transition (S : set (ccs lab)) (a : lab) : set (ccs lab)
|u := ∃ b, b ∈ S ∧ u ∈ (utransition u u a)

def transition_n : ccs lab → lab → ℕ → set (ccs lab)
|u a 0 := utransition u u a
|u a (k + 1) := set.union (transition_n u a (k)) 
  (map_transition (rest_utransition u u a) a)

def transition (p : ccs lab) (a : lab) (q : ccs lab): Prop := 
  ∃ n, q ∈ (transition_n p a n)

-- Bisimulación Fuerte

def bisimulation (r₁: ccs lab → ccs lab → Prop) := 
  ∀ x y, (∀ (a : lab) (x₁ : ccs lab), (r₁ x y ∧ transition x a x₁) → ∃ (y₁ : ccs lab), 
  (transition y a y₁ ∧ (r₁ x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab), 
  (r₁ x y ∧ transition y b y₁) → ∃ (x₁ : ccs lab), (transition x b x₁ ∧ (r₁ x₁ y₁)))

def bisimilar (x:ccs lab) (y:ccs lab) := 
  ∃ (s:ccs lab → ccs lab → Prop), (s x y) ∧ bisimulation s

def strong_bisimilarity: ccs lab → ccs lab → Prop
|p q := bisimilar p q


-- Vamos a asignar los símbolos usuales de ccs a nuestras definiciones
-- Para ello primero creamos unas funciones

def add : ccs lab → ccs lab → ccs lab 
|a b := psq (named a) (named b)

def par : ccs lab → ccs lab → ccs lab
|a b := pq (named a) (named b)

def lab_tran : lab → ccs lab → ccs lab
|a p := ap a (named p)

-- Asignamos ahora a cada símbolo su función

infix ` + `:50 := ccs.add

infix ` ∣ `:50 := ccs.par

infix ` . `:55 := ccs.lab_tran

infix ` ∼ `:40 := ccs.strong_bisimilarity

-- Comprobamos que las asignaciones de símbolos funcionen correctamente

#check ("input" . zer : ccs string)
#check (zer ∣ zer : ccs lab)
#check (re ∣ (named zer) : ccs lab)
#check ("output" . (zer + zer): ccs string) 
#check (zer) ∼ (zer + zer)
#check ("input" . zer ∣ zer : ccs string) ∼ zer
#check zer 

-- La definición de buffer1 intenta imitar B₀¹ del libro:
-- Reactive Systems: Modelling, Specification and Verification

def buffer1_0 : ccs string := "in" . ("out" . re)
def buffer1_1 : ccs string := "out" . ("in" . re)

-- La definición de buffer2 intenta imitar (B₀¹ | B₀¹)

def buffer2 : ccs string := buffer1_1 ∣ buffer1_0

-- La definición de buffer2_2 intenta imitar b₀² 

def buffer2_2_1 : ccs string := "in" . ("out" . re) + "out" . ( "in" . re)

end ccs


variables {lab X: Type u} [decidable_eq lab]


lemma ccs.bisimulation.identity_relation : ccs.bisimulation 
  (relation.identity_relation : ccs lab → ccs lab → Prop) := 
begin
  intro,
  intro,
  split,
  {
    intro,
    intro z,
    assume a₁,
    cases a₁,
    have h₁ : relation.identity_relation x y → y = x,
    tauto,
    have h₂ : y = x,
    tauto,
    fconstructor,
    exact z,
    split,
    finish,
    tauto,
  },
  {
    intro,
    intro z,
    assume a₁,
    cases a₁,
    have h₁ : relation.identity_relation x y → y = x,
    tauto,
    have h₂ : y = x,
    tauto,
    fconstructor,
    exact z,
    split,
    finish,
    tauto,
  },
end

lemma ccs.bisimilar.symmetric:  symmetric (ccs.bisimilar : ccs lab → ccs lab → Prop) :=
begin
  intro,
  intro,
  assume a,
  have h₁ : ∃ (r:ccs lab → ccs lab → Prop), (r x y) ∧ ccs.bisimulation r,
  from a,
  cases h₁,
  rename h₁_w r,
  let r₁ := relation.inverted_binary_relation r,
  fconstructor,
  exact r₁,
  cases h₁_h,
  have h₂ : ∀ x y, (∀ (a : lab) (x₁ : ccs lab), (r x y ∧ ccs.transition x a x₁) → 
    ∃ (y₁ : ccs lab), (ccs.transition y a y₁ ∧ (r x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab), 
    (r x y ∧ ccs.transition y b y₁) → ∃ (x₁ : ccs lab), (ccs.transition x b x₁ ∧ (r x₁ y₁))),
  from h₁_h_right,
  split,
  from h₁_h_left,
  suffices s₁ : ∀ x y, (∀ (a : lab) (x₁ : ccs lab), (r₁ x y ∧ ccs.transition x a x₁) → 
    ∃ (y₁ : ccs lab), (ccs.transition y a y₁ ∧ (r₁ x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab), 
    (r₁ x y ∧ ccs.transition y b y₁) → ∃ (x₁ : ccs lab), (ccs.transition x b x₁ ∧ (r₁ x₁ y₁))),
  tauto,
  intro z,
  intro w,
  have h₃ : (∀ (a : lab) (x₁ : ccs lab), (r w z ∧ ccs.transition w a x₁) → 
    ∃ (y₁ : ccs lab), (ccs.transition z a y₁ ∧ (r x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab), 
    (r w z ∧ ccs.transition z b y₁) → ∃ (x₁ : ccs lab), (ccs.transition w b x₁ ∧ (r x₁ y₁))),
  from h₂ w z,
  cases h₃,
  split,
  {
    intro l,
    intro z₁,
    assume a₁,
    have h₄ : r w z ∧ z.transition l z₁,
    from a₁,
    have h₅ : (r w z ∧ z.transition l z₁) → (∃ (w₁ : ccs lab), w.transition l w₁ ∧ r w₁ z₁),
    from h₃_right l z₁,
    from h₅ h₄,
  },
  {
    intro l,
    intro w₁,
    assume a₁,
    have h₄ : r w z ∧ w.transition l w₁,
    from a₁,
    have h₅ : (r w z ∧ w.transition l w₁) → (∃ (z₁ : ccs lab), z.transition l z₁ ∧ r w₁ z₁),
    from h₃_left l w₁,
    from h₅ h₄,
  },
end

lemma ccs.bisimilar.reflexive: reflexive (ccs.bisimilar : ccs lab → ccs lab → Prop) :=
begin
  intro,
  let r : (ccs lab → ccs lab → Prop) := relation.identity_relation,
  fconstructor,
  exact r,
  split,
  fconstructor,
  exact ccs.bisimulation.identity_relation,
end

lemma ccs.bisimilar_left: ∀ (r : ccs lab → ccs lab → Prop), ccs.bisimulation r → ∀ x y, 
  (∀ (a : lab) (x₁ : ccs lab), (r x y ∧ ccs.transition x a x₁) → ∃ (y₁ : ccs lab), 
  (ccs.transition y a y₁ ∧ (r x₁ y₁))) :=
begin
  intro,
  assume a₁,
  intro,
  intro,
  have h₁ : (∀ (a : lab) (x₁ : ccs lab), (r x y ∧ ccs.transition x a x₁) → 
    ∃ (y₁ : ccs lab), (ccs.transition y a y₁ ∧ (r x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab), 
    (r x y ∧ ccs.transition y b y₁) → ∃ (x₁ : ccs lab), (ccs.transition x b x₁ ∧ 
    (r x₁ y₁))),
  from a₁ x y,
  cases h₁,
  exact h₁_left,
end

lemma ccs.bisimilar_right: ∀ (r : ccs lab → ccs lab → Prop), ccs.bisimulation r → ∀ x y, 
  (∀ (a : lab) (y₁ : ccs lab), (r x y ∧ ccs.transition y a y₁) → ∃ (x₁ : ccs lab), 
  (ccs.transition x a x₁ ∧ (r x₁ y₁))) :=
begin
  intro,
  assume a₁,
  intro,
  intro,
  have h₁ : (∀ (a : lab) (x₁ : ccs lab), (r x y ∧ ccs.transition x a x₁) → 
    ∃ (y₁ : ccs lab), (ccs.transition y a y₁ ∧ (r x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab), 
    (r x y ∧ ccs.transition y b y₁) → ∃ (x₁ : ccs lab), (ccs.transition x b x₁ ∧ 
    (r x₁ y₁))),
  from a₁ x y,
  cases h₁,
  exact h₁_right,
end

lemma ccs.bisimilar.transitive: transitive (ccs.bisimilar : ccs lab → ccs lab → Prop) :=
begin
  intro,
  intro,
  intro,
  assume a₁,
  assume a₂,
  cases a₁,
  cases a₁_h,
  rename a₁_w r₁,
  cases a₂,
  cases a₂_h,
  rename a₂_w r₂,
  let r := relation.relation1 r₁ r₂,
  fconstructor,
  exact r,
  split,
  {
    fconstructor,
    exact y,
    tauto,
  },
  {
    intro q,
    intro w,
    split,
    {
      intro t,
      intro q₁,
      assume a₃,
      cases a₃,
      have h₁ : ∃ (e : ccs lab), r₁ q e ∧ r₂ e w,
      tauto,
      cases h₁,
      rename h₁_w e,
      have h₂ : ∀ x y, (∀ (a : lab) (x₁ : ccs lab), (r₁ x y ∧ ccs.transition x a x₁)
        → ∃ (y₁ : ccs lab), (ccs.transition y a y₁ ∧ (r₁ x₁ y₁))),
      exact ccs.bisimilar_left r₁ a₁_h_right,
      have h₃ : ∃ (e₁ : ccs lab), e.transition t e₁ ∧ r₁ q₁ e₁,
      have h₄ : r₁ q e ∧ ccs.transition q t q₁,
      tauto,
      from h₂ q e t q₁ h₄,
      cases h₃,
      rename h₃_w e₁,
      have h₅ : ∀ x y, (∀ (a : lab) (x₁ : ccs lab), (r₂ x y ∧ ccs.transition x a x₁)
        → ∃ (y₁ : ccs lab), (ccs.transition y a y₁ ∧ (r₂ x₁ y₁))),
      exact ccs.bisimilar_left r₂ a₂_h_right,
      have h₆ : ∃ (w₁ : ccs lab), w.transition t w₁ ∧ r₂ e₁ w₁,
      have h₇ : r₂ e w ∧ ccs.transition e t e₁,
      tauto,
      from h₅ e w t e₁ h₇,
      cases h₆,
      rename h₆_w w₁,
      fconstructor,
      exact w₁,
      cases h₆_h,
      split,
      exact h₆_h_left,
      cases h₃_h,
      fconstructor,
      exact e₁,
      tauto,
    },
    {
      intro t,
      intro w₁,
      assume a₃,
      cases a₃,
      have h₁ : ∃ (e : ccs lab), r₁ q e ∧ r₂ e w,
      tauto,
      cases h₁,
      rename h₁_w e,
      have h₂ : ∀ x y, (∀ (a : lab) (y₁ : ccs lab), (r₂ x y ∧ ccs.transition y a y₁)
        → ∃ (x₁ : ccs lab), (ccs.transition x a x₁ ∧ (r₂ x₁ y₁))),
      exact ccs.bisimilar_right r₂ a₂_h_right,
      have h₃ : ∃ (e₁ : ccs lab), e.transition t e₁ ∧ r₂ e₁ w₁,
      have h₄ : r₂ e w ∧ ccs.transition w t w₁,
      tauto,
      from h₂ e w t w₁ h₄,
      cases h₃,
      rename h₃_w e₁,
      have h₅ : ∀ x y, (∀ (a : lab) (y₁ : ccs lab), (r₁ x y ∧ ccs.transition y a y₁)
        → ∃ (x₁ : ccs lab), (ccs.transition x a x₁ ∧ (r₁ x₁ y₁))),
      exact ccs.bisimilar_right r₁ a₁_h_right,
      have h₆ : ∃ (q₁ : ccs lab), q.transition t q₁ ∧ r₁ q₁ e₁,
      have h₇ : r₁ q e ∧ ccs.transition e t e₁,
      tauto,
      from h₅ q e t e₁ h₇,
      cases h₆,
      rename h₆_w q₁,
      fconstructor,
      exact q₁,
      cases h₆_h,
      split,
      exact h₆_h_left,
      cases h₃_h,
      fconstructor,
      exact e₁,
      tauto,
    },
  },
end

theorem ccs.bismilar_relation.equivalence: equivalence 
  (ccs.strong_bisimilarity : ccs lab → ccs lab → Prop) :=
begin
  split,
  {
    intro,
    suffices s₁ : ccs.bisimilar x x,
    tauto,
    have h₁ : reflexive ccs.bisimilar → ccs.bisimilar x x,
    tauto,
    exact h₁ ccs.bisimilar.reflexive,
  },
  {
    split,
    {
      intro,
      intro,
      assume a₁,
      suffices s₁ : ccs.bisimilar y x,
      tauto,
      have h₁ : ccs.bisimilar x y,
      tauto,
      have h₂ : symmetric ccs.bisimilar → (ccs.bisimilar x y → ccs.bisimilar y x),
      tauto,
      exact h₂ ccs.bisimilar.symmetric h₁,
    },
    {
      intro,
      intro,
      intro,
      assume a₁,
      assume a₂,
      have h₁ : ccs.bisimilar x y,
      tauto,
      have h₂ : ccs.bisimilar y z,
      tauto,
      suffices s₁ : ccs.bisimilar x z,
      tauto,
      have h₃ : transitive ccs.bisimilar → (ccs.bisimilar x y ∧ ccs.bisimilar y z 
        → ccs.bisimilar x z),
      tauto,
      have h₄ : ccs.bisimilar x y ∧ ccs.bisimilar y z,
      tauto,
      exact h₃ ccs.bisimilar.transitive h₄,
    },
  },
end

theorem ccs.strong_bisimilarity.is_bisimulation : ccs.bisimulation 
  (ccs.strong_bisimilarity : ccs lab → ccs lab → Prop) :=
begin
  let r := (ccs.strong_bisimilarity : ccs lab → ccs lab → Prop),
  suffices s₁ : ccs.bisimulation r,
  tauto,
  intro,
  intro,
  split,
  {
    intro l,
    intro,
    assume a₁,
    cases a₁,
    have h₁ : ccs.bisimilar x y,
    tauto,
    have h₂ : ∃ (s:ccs lab → ccs lab → Prop), (s x y) ∧ ccs.bisimulation s,
    tauto,
    cases h₂,
    rename h₂_w s,
    suffices s₂ : ∃ (y₁ : ccs lab), y.transition l y₁ ∧ s x₁ y₁,
    {
      cases s₂,
      rename s₂_w y₁,
      fconstructor,
      exact y₁,
      split,
      tauto,
      fconstructor,
      exact s,
      tauto,
    },
    {
      have h₃ : (∀ (a : lab) (x₁ : ccs lab), (s x y ∧ x.transition a x₁) → ∃ (y₁ : ccs lab), 
        (y.transition a y₁ ∧ (s x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab), 
        (s x y ∧ y.transition b y₁) → ∃ (x₁ : ccs lab), (x.transition b x₁ ∧ (s x₁ y₁))),
      cases h₂_h,
      from h₂_h_right x y,
      cases h₃,
      have h₄ : s x y ∧ x.transition l x₁,
      tauto,
      from h₃_left l x₁ h₄,
    },
  },
  {
    intro l,
    intro,
    assume a₁,
    cases a₁,
    have h₁ : ccs.bisimilar x y,
    tauto,
    have h₂ : ∃ (s : ccs lab → ccs lab → Prop), (s x y) ∧ ccs.bisimulation s,
    tauto,
    cases h₂,
    rename h₂_w s,
    suffices s₂ : ∃ (x₁ : ccs lab), x.transition l x₁ ∧ s x₁ y₁,
    {
      cases s₂,
      rename s₂_w x₁,
      fconstructor,
      exact x₁,
      split,
      tauto,
      fconstructor,
      exact s,
      tauto,
    },
    {
      have h₃ : (∀ (a : lab) (x₁ : ccs lab), (s x y ∧ x.transition a x₁) → ∃ (y₁ : ccs lab), 
        (y.transition a y₁ ∧ (s x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab), 
        (s x y ∧ y.transition b y₁) → ∃ (x₁ : ccs lab), (x.transition b x₁ ∧ (s x₁ y₁))),
      cases h₂_h,
      from h₂_h_right x y,
      cases h₃,
      have h₄ : s x y ∧ y.transition l y₁,
      tauto,
      from h₃_right l y₁ h₄, 
    }
  },
end

lemma ccs.strong_bisimilarity.supset.bisimulation : ∀ (r:ccs lab → ccs lab → Prop),
  ccs.bisimulation r → (∀ x y, r x y → ccs.strong_bisimilarity x y) :=
begin
  intro r,
  assume a₁,
  intro x,
  intro y,
  assume a₂,
  fconstructor,
  exact r,
  tauto,
end

theorem ccs.strong_bisimilarity.is_largest_bisimulation : ∀ (s:ccs lab → ccs lab → Prop),
  ccs.bisimulation s → (cardinal.mk (relation.conj_relation (ccs.strong_bisimilarity :
  ccs lab → ccs lab → Prop))) >= (cardinal.mk (relation.conj_relation s)) :=
begin
  intro s,
  let r := (ccs.strong_bisimilarity : ccs lab → ccs lab → Prop),
  assume a₁,
  let cr := relation.conj_relation r,
  let cs := relation.conj_relation s,
  have h₁ : cs ⊆ cr,
  {
    intro,
    assume a₂,
    cases a,
    rename a_fst a,
    rename a_snd b,
    have h₂ : s a b,
    from a₂,
    suffices s₁ : r a b,
    from s₁,
    suffices s₂ : ccs.bisimilar a b,
    from s₂,
    fconstructor,
    exact s,
    split,
    from h₂,
    from a₁,
  },
  {
    norm_num,
    suffices s₁ : ∃ f : cs → cr, function.injective f,
    cases s₁,
    from cardinal.mk_le_of_injective s₁_h,
    have h₁ : ∀ a ∈ cs, a ∈ cr,
    tauto,
    let f : cs → cr := set.inclusion h₁,
    fconstructor,
    exact f,
    from set.inclusion_injective h₁,
  },
end

theorem ccs.strong_bisimilarity.property : ∀ (x y : ccs lab), ( ( ∀ (t : lab) (x₁ : ccs lab), 
  x.transition t x₁ → ∃ (y₁ : ccs lab), y.transition t y₁ ∧ ccs.strong_bisimilarity x₁ y₁ ) 
  ∧ ( ∀ (t : lab) (y₁ : ccs lab), y.transition t y₁ → ∃ (x₁ : ccs lab), x.transition t x₁ ∧ 
  ccs.strong_bisimilarity x₁ y₁ ) ) → ccs.strong_bisimilarity x y :=
begin
  intro,
  intro,
  assume a₁,
  cases a₁,
  let r := relation.join_relations (relation.relation2 x y) ccs.strong_bisimilarity,
  let con_r := (set.union (relation.conj_relation (relation.relation2 x y)) 
  (relation.conj_relation ccs.strong_bisimilarity)),
  suffices s₁ : ccs.bisimulation r,
  {
    suffices s₂ : r x y,
    from ccs.strong_bisimilarity.supset.bisimulation r s₁ x y s₂,
    fconstructor,
    split,
    trivial,
    trivial,
  },
  {
    intro c,
    intro d,
    split,
    {
      intro l,
      intro c₁,
      assume a₂,
      cases a₂,
      have ca₁ : c = x ∨ c ≠ x,
      tauto,
      cases ca₁,
      have ca₂ : d = x ∨ d = y ∨ (d ≠ x ∧ d ≠ y),
      tauto,
      cases ca₂,
      {
        fconstructor,
        exact c₁,
        split,
        subst ca₁,
        subst ca₂,
        from a₂_right,
        have h₁ : ccs.strong_bisimilarity c₁ c₁,
        fconstructor,
        exact relation.identity_relation,
        split,
        tauto,
        from ccs.bisimulation.identity_relation,
        suffices s₂ : (c₁,c₁) ∈ con_r,
        tauto,
        suffices s₃ : (c₁,c₁) ∈ (relation.conj_relation 
          (ccs.strong_bisimilarity : ccs lab → ccs lab → Prop)), 
        exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₁,
        fconstructor,
        exact relation.identity_relation,
        split,
        tauto,
        from ccs.bisimulation.identity_relation,
      },
      {
        cases ca₂,
        {
          have h₂ : ∃ (d₁ : ccs lab) , y.transition l d₁ ∧ ccs.strong_bisimilarity c₁ d₁,
          have h₃ : x.transition l c₁,
          subst ca₁,
          from a₂_right,
          from a₁_left l c₁ h₃,
          cases h₂,
          fconstructor,
          exact h₂_w,
          cases h₂_h,
          split,
          subst ca₂,
          from h₂_h_left,
          exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₂_h_right,
        },
        {
          cases ca₂,
          suffices h₄ : (c,d) ∈ (relation.conj_relation 
            (ccs.strong_bisimilarity : ccs lab → ccs lab → Prop)),
          {
            have h₅ : ccs.strong_bisimilarity c d,
            tauto,
            have h₆ : ∃ (s : ccs lab → ccs lab → Prop), (s c d) ∧ ccs.bisimulation s,
            from h₅,
            cases h₆,
            rename h₆_w s,
            cases h₆_h,
            have h₇ : (∀ t (c₁ : ccs lab), (s c d ∧ c.transition t c₁) → ∃ (d₁ : ccs lab), 
              (d.transition t d₁ ∧ (s c₁ d₁))) ∧ (∀ t (d₁ : ccs lab), (s c d ∧ d.transition 
              t d₁) → ∃ (c₁ : ccs lab), (c.transition t c₁ ∧ (s c₁ d₁))),
            from h₆_h_right c d,
            cases h₇,
            have h₈ : s c d ∧ c.transition l c₁,
            split,
            from h₆_h_left,
            from a₂_right,
            have h₉ : ∃ (d₁ : ccs lab), d.transition l d₁ ∧ s c₁ d₁,
            from h₇_left l c₁ h₈,
            cases h₉,
            rename h₉_w d₁,
            fconstructor,
            exact d₁,
            split,
            tauto,
            have h₁₀ : ccs.bisimilar c₁ d₁,
            fconstructor,
            exact s,
            tauto,
            exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₁₀,
          },
          {
            have h₁ : ccs.strong_bisimilarity c d,
            have h₂ : r c d → (c = x ∧ d = y) ∨ ccs.strong_bisimilarity c d,
            exact (set.mem_union (c, d) (relation.conj_relation (relation.relation2 x y))
              (relation.conj_relation (ccs.strong_bisimilarity))).mp,
            have h₃ : (c = x ∧ d = y) ∨ ccs.strong_bisimilarity c d,
            from h₂ a₂_left,
            tauto,
            from h₁,
          },
        },
      },
      {
        have h₁ : r c d → (c = x ∧ d = y) ∨ ccs.strong_bisimilarity c d,
        exact (set.mem_union (c, d) (relation.conj_relation (relation.relation2 x y))
          (relation.conj_relation (ccs.strong_bisimilarity))).mp,
        have h₂ : (c = x ∧ d = y) ∨ ccs.strong_bisimilarity c d,
        from h₁ a₂_left,
        have h₃ : ccs.strong_bisimilarity c d,
        tauto,
        have h₄ : ∃ (s : ccs lab → ccs lab → Prop), (s c d) ∧ ccs.bisimulation s,
        from h₃,
        cases h₄,
        rename h₄_w s,
        cases h₄_h,
        have h₅ : (∀ a (x₁ : ccs lab), (s c d ∧ c.transition a x₁) → ∃ (y₁ : ccs lab), 
          (d.transition a y₁ ∧ (s x₁ y₁))) ∧ (∀ b (y₁ : ccs lab), (s c d ∧ d.transition 
          b y₁) → ∃ (x₁ : ccs lab), (c.transition b x₁ ∧ (s x₁ y₁))),
        from h₄_h_right c d,
        cases h₅,
        have h₆ : s c d ∧ c.transition l c₁,
        split,
        from h₄_h_left,
        from a₂_right,
        have h₇ : ∃ (y₁ : ccs lab), d.transition l y₁ ∧ s c₁ y₁,
        from h₅_left l c₁ h₆,
        cases h₇,
        rename h₇_w d₁,
        fconstructor,
        exact d₁,
        split,
        tauto,
        have h₈ : ccs.bisimilar c₁ d₁,
        fconstructor,
        exact s,
        tauto,
        exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₈,
      },
    },
    {
      intro l,
      intro d₁,
      assume a₂,
      cases a₂,
      have ca₁ : d = y ∨ d ≠ y,
      tauto,
      cases ca₁,
      have ca₂ : c = y ∨ c = x ∨ (c≠x ∧ c≠y),
      tauto,
      cases ca₂,
      {
        fconstructor,
        exact d₁,
        split,
        have h₁ : c = d,
        subst ca₂,
        tauto,
        subst h₁,
        from a₂_right,
        have h₁ : ccs.strong_bisimilarity d₁ d₁,
        fconstructor,
        exact relation.identity_relation,
        split,
        tauto,
        from ccs.bisimulation.identity_relation,
        suffices h₁ : (d₁,d₁) ∈ con_r,
        tauto,
        suffices h₂ : (d₁,d₁)∈ (relation.conj_relation 
          (ccs.strong_bisimilarity : ccs lab → ccs lab → Prop)),
        exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₁,
        fconstructor,
        exact relation.identity_relation,
        split,
        tauto,
        from ccs.bisimulation.identity_relation,
      },
      {
        cases ca₂,
        {
          have h₁ : ∃(c₁ : ccs lab), x.transition l c₁ ∧ ccs.strong_bisimilarity c₁ d₁,
          have h₂ : y.transition l d₁,
          subst ca₁,
          from a₂_right,
          from a₁_right l d₁ h₂,
          cases h₁,
          fconstructor,
          exact h₁_w,
          cases h₁_h,
          split,
          subst ca₂,
          from h₁_h_left,
          exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₁_h_right,
        },
        {
          cases ca₂,
          suffices h₁ : (c,d)∈ (relation.conj_relation 
            (ccs.strong_bisimilarity : ccs lab → ccs lab → Prop)),
          {
            have h₂ : ccs.strong_bisimilarity c d,
            tauto,
            have h₃ : ∃ (s : ccs lab → ccs lab → Prop), (s c d) ∧ ccs.bisimulation s,
            from h₂,
            cases h₃,
            rename h₃_w s,
            cases h₃_h,
            have h₄ : (∀ t (x₁ : ccs lab), (s c d ∧ c.transition 
              t x₁) → ∃ (c₁ : ccs lab), (d.transition t c₁ ∧ (s x₁ c₁))) ∧ 
              (∀ t (d₁ : ccs lab), (s c d ∧ d.transition t d₁) → ∃ (c₁ : ccs lab), 
              (c.transition t c₁ ∧ (s c₁ d₁))),
            from h₃_h_right c d,
            cases h₄,
            have h₅ : s c d ∧ d.transition l d₁,
            split,
            from h₃_h_left,
            from a₂_right,
            have h₆ : ∃ (y₁ : ccs lab), c.transition l y₁ ∧ s y₁ d₁,
            from h₄_right l d₁ h₅,
            cases h₆,
            rename h₆_w c₁,
            fconstructor,
            exact c₁,
            split,
            tauto,
            have h₇ : ccs.bisimilar c₁ d₁,
            fconstructor,
            exact s,
            tauto,
            exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₇,
          },
          {
            have h₁ : ccs.strong_bisimilarity c d,
            have h₂ : r c d → (c = x ∧ d = y) ∨ ccs.strong_bisimilarity c d,
            exact (set.mem_union (c, d) (relation.conj_relation (relation.relation2 x y))
              (relation.conj_relation (ccs.strong_bisimilarity))).mp,
            have h₃ : (c = x ∧ d = y) ∨ ccs.strong_bisimilarity c d,
            from h₂ a₂_left,
            tauto,
            from h₁,
          },
        },
      },
      {
        have h₁ : r c d → (c = x ∧ d = y) ∨ ccs.strong_bisimilarity c d,
        exact (set.mem_union (c, d) (relation.conj_relation (relation.relation2 x y))
          (relation.conj_relation (ccs.strong_bisimilarity))).mp,
        have h₂ : (c = x ∧ d = y) ∨ ccs.strong_bisimilarity c d,
        from h₁ a₂_left,
        have h₃ : ccs.strong_bisimilarity c d,
        tauto,
        have h₄ : ∃ (s : ccs lab → ccs lab → Prop), (s c d) ∧ ccs.bisimulation s,
        from h₃,
        cases h₄,
        rename h₄_w s,
        cases h₄_h,
        have h₅ : (∀ t (y₁ : ccs lab), (s c d ∧ c.transition t y₁) → ∃ (d₁ : ccs lab), 
          (d.transition t d₁ ∧ (s y₁ d₁))) ∧ (∀ t (d₁ : ccs lab), (s c d ∧ d.transition 
          t d₁) → ∃ (y₁ : ccs lab), (c.transition t y₁ ∧ (s y₁ d₁))),
        from h₄_h_right c d,
        cases h₅,
        have h₆ : s c d ∧ d.transition l d₁,
        split,
        from h₄_h_left,
        from a₂_right,
        have h₇ : ∃ (y₁ : ccs lab), c.transition l y₁ ∧ s y₁ d₁,
        from h₅_right l d₁ h₆,
        cases h₇,
        rename h₇_w c₁,
        fconstructor,
        exact c₁,
        split,
        tauto,
        have h₈ : ccs.bisimilar c₁ d₁,
        fconstructor,
        exact s,
        tauto,
        exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₈,
      },
    },
  },
end

lemma relation.join_relations_right : ∀ (r s : X → X → Prop) (x y : X), s x y →
  (relation.join_relations r s) x y :=
begin
  intro,
  intro,
  intro,
  intro,
  assume a₁,
  let t := relation.join_relations r s,
  suffices s₁ : t x y,
  tauto,
  exact (relation.conj_relation (r)).mem_union_right a₁,
end

lemma ccs.transition_ap : ∀ (x : ccs lab) (t : lab), ccs.transition (t . (named x)) t x :=
begin
  intro,
  intro,
  fconstructor,
  exact 0,
  suffices s₁ : x ∈ ccs.utransition (t . (named x)) (t . (named x)) t,
  tauto,
  have h₁ : (ccs.sust_simp (named x) (t . (named x))) = x,
  fconstructor,
  suffices s₂ : (ccs.sust_simp (named x) (t . (named x))) ∈ ccs.utransition 
    (t . (named x)) (t . (named x)) t,
  tauto,
  have h₂ : ccs.utransition (t . (named x)) (t . (named x)) t = {(ccs.sust_simp (named x) 
    (t . (named x)))},
  {
    reduce ccs.utransition, 
  },
  {
    sorry,
  },
end