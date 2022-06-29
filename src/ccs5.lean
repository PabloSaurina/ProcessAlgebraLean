import data.fintype.basic
import set_theory.cardinal
import lts

universe u 

mutual inductive uccs, ccs (lab : Type u)
with uccs : Type u
|zer : uccs
|ap (a:lab) (u:uccs) : uccs
|pq (p:uccs) (q:uccs) : uccs
|psq (p:uccs) (q:uccs) : uccs
|re : uccs
|named (n : ccs): uccs
with ccs : Type u 
|de (u:uccs) : ccs

export uccs (zer ap pq psq re named)
export ccs (de)

namespace ccs

variables {lab : Type u} [decidable_eq lab]

def sust: uccs lab → ccs lab → uccs lab
|zer n:= zer
|(ap a u) n := (ap a (sust u n))
|(pq p q) n := (pq (sust p n) (sust q n))
|(psq p q) n := (psq (sust p n) (sust q n))
|re n := named n
|(named n) m := named n

def simp: uccs lab → ccs lab
|(named n) := n
|a := de a

def sust_simp: uccs lab → ccs lab → ccs lab
|u n := simp (sust u n)

def combinaciones (A B : set (ccs lab)) (a b : ccs lab): set (ccs lab)
|(de (pq (named c) (named d))) := (c ∈ A ∧ d ∈ B) ∨ (c ∈ A ∧ d = b) ∨ (c = a ∧ b ∈ B)
|p := ff

def ucomp: ccs lab → uccs lab
|(de u) := u

def comp: uccs lab → ccs lab
|u := (de u)

def utransition : ccs lab → uccs lab → lab → set (ccs lab)
|n zer a := {}
|n (ap a (psq p q)) b := if a = b then {sust_simp p n,sust_simp q n,sust_simp (psq p q) n} else {}
|n (ap a (pq p q)) b := if a = b then {sust_simp (pq p q) n} else {}
|n (ap a u) b := if a = b then {sust_simp u n} else {}
|n (pq p q) a := combinaciones (utransition n p a) (utransition n q a) 
  (sust_simp p n) (sust_simp q n)
|n (psq p q) a := set.union (utransition n p a) (utransition n q a)
|n (re) a := {}
|n (named m) a := {}

def rest_utransition : ccs lab → uccs lab → lab → set (ccs lab)
|n zer a := {}
|n (ap a u) b := {}
|n (pq p q) a := combinaciones (rest_utransition n p a) (rest_utransition n q a) 
  (sust_simp p n) (sust_simp q n)
|n (psq p q) a := set.union (rest_utransition n p a) (rest_utransition n q a)
|n re a := {}
|n (named m) a := {m}

def map_transition (S : set (ccs lab)) (a : lab) : set (ccs lab)
|(de u) := ∃ b, b ∈ S ∧ (de u) ∈ (utransition (de u) u a)

def transition_n : ccs lab → lab → ℕ → set (ccs lab)
|(de u) a 0 := utransition (de u) u a
|(de u) a (k + 1) := set.union (transition_n (de u) a (k)) 
  (map_transition (rest_utransition (de u) u a) a)

def transition (p : ccs lab) (a : lab) (q : ccs lab): Prop := 
  ∃ n, q ∈ (transition_n p a n)

-- Bisimulación Fuerte

def strong_bisimulation (r₁: ccs lab → ccs lab → Prop) := 
  ∀ x y, (∀ (a : lab) (x₁ : ccs lab), (r₁ x y ∧ transition x a x₁) → ∃ (y₁ : ccs lab), 
  (transition y a y₁ ∧ (r₁ x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab), 
  (r₁ x y ∧ transition y b y₁) → ∃ (x₁ : ccs lab), (transition x b x₁ ∧ (r₁ x₁ y₁)))

def bisimilar (x:ccs lab) (y:ccs lab) := 
  ∃ (s:ccs lab → ccs lab → Prop), (s x y) ∧ strong_bisimulation s

def bisimilar_relation: ccs lab → ccs lab → Prop
|p q := bisimilar p q


-- Vamos a asignar los símbolos usuales de ccs a nuestras definiciones
-- Para ello primero creamos unas funciones

def add : ccs lab → ccs lab → ccs lab 
|a b := de (psq (named a) (named b))

def par : ccs lab → ccs lab → ccs lab
|a b := de (pq (named a) (named b))

def lab_tran : lab → ccs lab → ccs lab
|a p := de (ap a (named p))

-- Repetimos lo mismo pero para uccs

def uadd : uccs lab → uccs lab → uccs lab 
|a b := psq a b

def upar : uccs lab → uccs lab → uccs lab
|a b := pq a b

def ulab_tran : lab → uccs lab → uccs lab
|a p := ap a p

-- Asignamos ahora a cada símbolo su función

infix ` + `:50 := ccs.add
infix ` + `:50 := ccs.uadd

infix ` ∣ `:50 := ccs.par
infix ` ∣ `:50 := ccs.upar

infix ` . `:55 := ccs.lab_tran
infix ` . `:55 := ccs.ulab_tran

infix ` ∼ `:40 := ccs.bisimilar_relation

prefix ` ℂ `:30 := ccs.comp

-- Comprobamos que las asignaciones de símbolos funcionen correctamente

#check ("input" . zer : uccs string)
#check (zer ∣ zer : uccs lab)
#check ((ℂ re) ∣ (ℂ named (de zer)) : ccs lab)
#check ("output" . (zer + zer): uccs string) 
#check (ℂ zer) ∼ (ℂ zer + zer)
#check (ℂ "input" . zer ∣ zer : ccs string) ∼ (de zer)
#check ℂ zer 


-- La definición de buffer1 intenta imitar B₀¹ del libro:
-- Reactive Systems: Modelling, Specification and Verification

def buffer1_0 : ccs string := ℂ "in" . ("out" . re)
def buffer1_1 : ccs string := ℂ "out" . ("in" . re)

-- La definición de buffer2 intenta imitar (B₀¹ | B₀¹)

def buffer2 : ccs string := buffer1_1 ∣ buffer1_0

-- La definición de buffer2_2 intenta imitar b₀² 

def buffer2_2_1 : ccs string := ℂ "in" . ("out" . re) + "out" . ( "in" . re)

end ccs


variables {lab : Type u} [decidable_eq lab]

lemma ccs.strong_bisimulation.identity_relation : ccs.strong_bisimulation 
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
  have h₁ : ∃ (r:ccs lab → ccs lab → Prop), (r x y) ∧ ccs.strong_bisimulation r,
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

theorem ccs.bismilar_relation.equivalence: equivalence 
  (ccs.bisimilar_relation : ccs lab → ccs lab → Prop) :=
begin
  split,
  {
    intro c,
    let r : (ccs lab → ccs lab → Prop) := relation.identity_relation,
    suffices s₁ : c.bisimilar c,
    exact s₁,
    fconstructor,
    exact r,
    split,
    tauto,
    suffices s₂ : ∀ x y, (∀ (a : lab) (x₁ : ccs lab), (r x y ∧ x.transition a x₁) → ∃ 
    (y₁ : ccs lab), (y.transition a y₁ ∧ (r x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab),
    (r x y ∧ y.transition b y₁) → ∃ (x₁ : ccs lab), (x.transition b x₁ ∧ (r x₁ y₁))),
    exact s₂,
    intro x,
    intro y,
    split,
    {
      intro l,
      intro,
      assume a₁,
      fconstructor,
      exact x₁,
      cases a₁,
      have h₁ : x = y,
      tauto,
      split,
      finish,
      tauto,
    },
    {
      intro l,
      intro,
      assume a₁,
      fconstructor,
      exact y₁,
      cases a₁,
      have h₁ : y = x,
      tauto,
      split,
      finish,
      tauto,
    },
  },
  {
    split,
    {
      intro,
      intro,
      assume a₁,
      suffices s₁ : y.bisimilar x,
      tauto,
      have h₁ : x.bisimilar y,
      tauto,
      have h₂ : symmetric (ccs.bisimilar : ccs lab → ccs lab → Prop),
      from ccs.bisimilar.symmetric,
      exact h₂ h₁,
    },
    {
      intro x,
      intro y,
      intro z,
      assume a₁,
      assume a₂,
      cases a₁,
      cases a₂,
      rename a₁_w r₁,
      rename a₂_w r₂,
      let r : (ccs lab → ccs lab → Prop):=  relation.relation1 r₁ r₂,
      suffices s₁ : x.bisimilar z,
      tauto,
      suffices s₂ : ∃ (s:ccs lab → ccs lab → Prop), (s x z) ∧ ccs.strong_bisimulation s,
      tauto,
      fconstructor,
      exact r,
      split,
      {
        fconstructor,
        exact y,
        split,
        tauto,
        tauto,
      },
      {
        intro c,
        intro d,
        split,
        {
          intro l,
          intro c₁,
          assume a₃,
          cases a₃,
          have h₁ : ∃ e, r₁ c e ∧ r₂ e d,
          tauto,
          cases h₁,
          rename h₁_w e,
          have h₂ : (∀ (a : lab) (x₁ : ccs lab), r₁ c e ∧ c.transition a x₁ → 
            (∃ (y₁ : ccs lab), e.transition a y₁ ∧ r₁ x₁ y₁)) ∧ ∀ (b : lab) (y₁ 
            : ccs lab), r₁ c e ∧ e.transition b y₁ → (∃ (x₁ : ccs lab), c.transition 
            b x₁ ∧ r₁ x₁ y₁),
          cases a₁_h,
          from a₁_h_right c e,
          cases h₂,
          have h₃ : (∀ (a : lab) (x₁ : ccs lab), r₂ e d ∧ e.transition a x₁ → 
            (∃ (y₁ : ccs lab), d.transition a y₁ ∧ r₂ x₁ y₁)) ∧ ∀ (b : lab) (y₁ 
            : ccs lab), r₂ e d ∧ d.transition b y₁ → (∃ (x₁ : ccs lab), e.transition 
            b x₁ ∧ r₂ x₁ y₁),
          cases a₂_h,
          from a₂_h_right e d,
          cases h₃,
          have h₄ : ∃ (e₁ : ccs lab), e.transition l e₁ ∧ r₁ c₁ e₁,
          cases h₁_h,
          have h₅ : r₁ c e ∧ c.transition l c₁,
          tauto,
          from h₂_left l c₁ h₅,
          cases h₄,
          rename h₄_w e₁,
          have h₆ : ∃ (d₁ : ccs lab), d.transition l d₁ ∧ r₂ e₁ d₁,
          cases h₁_h,
          cases h₄_h,
          have h₇ : r₂ e d ∧ e.transition l e₁,
          tauto,
          from h₃_left l e₁ h₇,
          cases h₆,
          rename h₆_w d₁,
          fconstructor,
          exact d₁,
          cases h₄_h,
          cases h₆_h,
          split,
          exact h₆_h_left,
          fconstructor,
          exact e₁,
          tauto,
        },
        {
          intro l,
          intro d₁,
          assume a₃,
          cases a₃,
          have h₁ : ∃ e, r₁ c e ∧ r₂ e d,
          tauto,
          cases h₁,
          rename h₁_w e,
          have h₂ : (∀ (a : lab) (x₁ : ccs lab), r₁ c e ∧ c.transition a x₁ → 
            (∃ (y₁ : ccs lab), e.transition a y₁ ∧ r₁ x₁ y₁)) ∧ ∀ (b : lab) (y₁ 
            : ccs lab), r₁ c e ∧ e.transition b y₁ → (∃ (x₁ : ccs lab), c.transition 
            b x₁ ∧ r₁ x₁ y₁),
          cases a₁_h,
          from a₁_h_right c e,
          cases h₂,
          have h₃ : (∀ (a : lab) (x₁ : ccs lab), r₂ e d ∧ e.transition a x₁ → 
            (∃ (y₁ : ccs lab), d.transition a y₁ ∧ r₂ x₁ y₁)) ∧ ∀ (b : lab) (y₁ 
            : ccs lab), r₂ e d ∧ d.transition b y₁ → (∃ (x₁ : ccs lab), e.transition 
            b x₁ ∧ r₂ x₁ y₁),
          cases a₂_h,
          from a₂_h_right e d,
          cases h₃,
          have h₄ : ∃ (e₁ : ccs lab), e.transition l e₁ ∧ r₂ e₁ d₁,
          cases h₁_h,
          have h₅ : r₂ e d ∧ d.transition l d₁,
          tauto,
          from h₃_right l d₁ h₅,
          cases h₄,
          rename h₄_w e₁,
          have h₆ : ∃ (c₁ : ccs lab), c.transition l c₁ ∧ r₁ c₁ e₁,
          cases h₁_h,
          cases h₄_h,
          have h₇ : r₁ c e ∧ e.transition l e₁,
          tauto,
          from h₂_right l e₁ h₇,
          cases h₆,
          rename h₆_w c₁,
          fconstructor,
          exact c₁,
          split,
          tauto,
          fconstructor,
          exact e₁,
          tauto,
        },
      },
    },
  }
end

theorem ccs.bisimilar_relation.is_strong_bisimulation : ccs.strong_bisimulation 
  (ccs.bisimilar_relation : ccs lab → ccs lab → Prop) :=
begin
  let r := (ccs.bisimilar_relation : ccs lab → ccs lab → Prop),
  suffices s₁ : ccs.strong_bisimulation r,
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
    have h₂ : ∃ (s:ccs lab → ccs lab → Prop), (s x y) ∧ ccs.strong_bisimulation s,
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
    have h₂ : ∃ (s : ccs lab → ccs lab → Prop), (s x y) ∧ ccs.strong_bisimulation s,
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

lemma ccs.bisimilar_relation.supset.strong_bisimulation : ∀ (r:ccs lab → ccs lab → Prop),
  ccs.strong_bisimulation r → (∀ x y, r x y → ccs.bisimilar_relation x y) :=
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

theorem ccs.bisimilar_relation.is_largest_strong_bisimulation : ∀ (s:ccs lab → ccs lab → Prop),
  ccs.strong_bisimulation s → (cardinal.mk (relation.conj_relation (ccs.bisimilar_relation :
  ccs lab → ccs lab → Prop))) >= (cardinal.mk (relation.conj_relation s)) :=
begin
  intro s,
  let r := (ccs.bisimilar_relation : ccs lab → ccs lab → Prop),
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

theorem ccs.bisimilar_relation.property : ∀ (x y : ccs lab), ( ( ∀ (t : lab) (x₁ : ccs lab), 
  x.transition t x₁ → ∃ (y₁ : ccs lab), y.transition t y₁ ∧ ccs.bisimilar_relation x₁ y₁ ) 
  ∧ ( ∀ (t : lab) (y₁ : ccs lab), y.transition t y₁ → ∃ (x₁ : ccs lab), x.transition t x₁ ∧ 
  ccs.bisimilar_relation x₁ y₁ ) ) → ccs.bisimilar_relation x y :=
begin
  intro,
  intro,
  assume a₁,
  cases a₁,
  let r := relation.join_relations (relation.relation2 x y) ccs.bisimilar_relation,
  let con_r := (set.union (relation.conj_relation (relation.relation2 x y)) 
  (relation.conj_relation ccs.bisimilar_relation)),
  suffices s₁ : ccs.strong_bisimulation r,
  {
    suffices s₂ : r x y,
    from ccs.bisimilar_relation.supset.strong_bisimulation r s₁ x y s₂,
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
        have h₁ : ccs.bisimilar_relation c₁ c₁,
        fconstructor,
        exact relation.identity_relation,
        split,
        tauto,
        from ccs.strong_bisimulation.identity_relation,
        suffices s₂ : (c₁,c₁) ∈ con_r,
        tauto,
        suffices s₃ : (c₁,c₁) ∈ (relation.conj_relation 
          (ccs.bisimilar_relation : ccs lab → ccs lab → Prop)), 
        exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₁,
        fconstructor,
        exact relation.identity_relation,
        split,
        tauto,
        from ccs.strong_bisimulation.identity_relation,
      },
      {
        cases ca₂,
        {
          have h₂ : ∃ (d₁ : ccs lab) , y.transition l d₁ ∧ ccs.bisimilar_relation c₁ d₁,
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
            (ccs.bisimilar_relation : ccs lab → ccs lab → Prop)),
          {
            have h₅ : ccs.bisimilar_relation c d,
            tauto,
            have h₆ : ∃ (s : ccs lab → ccs lab → Prop), (s c d) ∧ ccs.strong_bisimulation s,
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
            have h₁ : ccs.bisimilar_relation c d,
            have h₂ : r c d → (c = x ∧ d = y) ∨ ccs.bisimilar_relation c d,
            exact (set.mem_union (c, d) (relation.conj_relation (relation.relation2 x y))
              (relation.conj_relation (ccs.bisimilar_relation))).mp,
            have h₃ : (c = x ∧ d = y) ∨ ccs.bisimilar_relation c d,
            from h₂ a₂_left,
            tauto,
            from h₁,
          },
        },
      },
      {
        have h₁ : r c d → (c = x ∧ d = y) ∨ ccs.bisimilar_relation c d,
        exact (set.mem_union (c, d) (relation.conj_relation (relation.relation2 x y))
          (relation.conj_relation (ccs.bisimilar_relation))).mp,
        have h₂ : (c = x ∧ d = y) ∨ ccs.bisimilar_relation c d,
        from h₁ a₂_left,
        have h₃ : ccs.bisimilar_relation c d,
        tauto,
        have h₄ : ∃ (s : ccs lab → ccs lab → Prop), (s c d) ∧ ccs.strong_bisimulation s,
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
        have h₁ : ccs.bisimilar_relation d₁ d₁,
        fconstructor,
        exact relation.identity_relation,
        split,
        tauto,
        from ccs.strong_bisimulation.identity_relation,
        suffices h₁ : (d₁,d₁) ∈ con_r,
        tauto,
        suffices h₂ : (d₁,d₁)∈ (relation.conj_relation 
          (ccs.bisimilar_relation : ccs lab → ccs lab → Prop)),
        exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₁,
        fconstructor,
        exact relation.identity_relation,
        split,
        tauto,
        from ccs.strong_bisimulation.identity_relation,
      },
      {
        cases ca₂,
        {
          have h₁ : ∃(c₁ : ccs lab), x.transition l c₁ ∧ ccs.bisimilar_relation c₁ d₁,
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
            (ccs.bisimilar_relation : ccs lab → ccs lab → Prop)),
          {
            have h₂ : ccs.bisimilar_relation c d,
            tauto,
            have h₃ : ∃ (s : ccs lab → ccs lab → Prop), (s c d) ∧ ccs.strong_bisimulation s,
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
            have h₁ : ccs.bisimilar_relation c d,
            have h₂ : r c d → (c = x ∧ d = y) ∨ ccs.bisimilar_relation c d,
            exact (set.mem_union (c, d) (relation.conj_relation (relation.relation2 x y))
              (relation.conj_relation (ccs.bisimilar_relation))).mp,
            have h₃ : (c = x ∧ d = y) ∨ ccs.bisimilar_relation c d,
            from h₂ a₂_left,
            tauto,
            from h₁,
          },
        },
      },
      {
        have h₁ : r c d → (c = x ∧ d = y) ∨ ccs.bisimilar_relation c d,
        exact (set.mem_union (c, d) (relation.conj_relation (relation.relation2 x y))
          (relation.conj_relation (ccs.bisimilar_relation))).mp,
        have h₂ : (c = x ∧ d = y) ∨ ccs.bisimilar_relation c d,
        from h₁ a₂_left,
        have h₃ : ccs.bisimilar_relation c d,
        tauto,
        have h₄ : ∃ (s : ccs lab → ccs lab → Prop), (s c d) ∧ ccs.strong_bisimulation s,
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