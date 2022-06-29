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

def or_transition: ccs lab → ccs lab → lab → ccs lab → Prop
|or (ap b c) a u := a = b ∧ (sust_simp (simp c) or) = u
|or (psq p q) a u := or_transition or p a u ∨ or_transition or q a u
|or (pq p q) a u := (∃ c, or_transition or p a c ∧ u = (pq c q)) ∨ (∃ c, 
  or_transition or q a c ∧ u = (pq p c)) ∨ (∃ c d, or_transition or p a c 
  ∧ or_transition or q a d ∧ u = (pq c d))
|or (named m) a u := or_transition m m a u
|_ _ _ _ := ff

def transition: ccs lab → lab → ccs lab → Prop 
|or a u := or_transition or or a u

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




-- Funciones auxiliar para una demostración

def funcion1 : ccs lab → ccs lab → ccs lab → Prop 
|a c u := u = (a + c)

def funcion2 : ccs lab → ccs lab → ccs lab → Prop 
|a c u := u = (c + a)

def relation1 : ccs lab → ccs lab → Prop
|(pq (named x) (named z)) (pq (named y) (named w)) := x ∼ y ∧ z = w
|(pq x z) (pq y w) := x ∼ y ∧ z = w
|_ _ := false

end ccs


-- Para las proximas demostraciones utilizaremos ciertas relaciones que hay que definir
-- previamente. Realizamos esto dentro del espacio 'relation'

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
  tauto,
  suffices s₁ : ccs.simp (ccs.sust x.named (t . x.named)) = x,
  tauto,
  have h₂ : ccs.simp x.named = x,
  tauto,
  tauto,
end

lemma ccs.transtion_ap_only : ∀ (x y : ccs lab) (t : lab), ccs.transition (t . (named x)) t y
  → y = x :=
begin
  intro,
  intro,
  intro,
  assume a₁,
  cases a₁,
  suffices s₁ : x.named.sust_simp (t . x.named) = x,
  tauto,
  suffices s₂ : ccs.simp (ccs.sust x.named (t . x.named)) = x,
  tauto,
  have h₁ : ccs.sust x.named (t . x.named) = x.named,
  {
    fconstructor,
  },
  {
    suffices s₃ : ccs.simp x.named = x,
    tauto,
    tauto,
  },
end

lemma ccs.transition_ap_a : ∀ (x y: ccs lab) (t l : lab), ccs.transition (t . (named x)) 
  l y → l = t :=
begin
  intro,
  intro,
  intro,
  intro,
  assume a₁,
  cases a₁,
  tauto,
end

theorem ccs.property_ap_bisimilar : ∀ (x y : ccs lab) (t : lab), x ∼ y → (t . (named x)) ∼ 
  (t . (named y)) := 
begin
  intro,
  intro,
  intro,
  assume a₁,
  cases a₁,
  cases a₁_h,
  rename a₁_w r,
  let s := relation.join_relations (relation.relation2 (t . (named x)) (t . (named y))) r,
  fconstructor,
  exact s,
  split,
  {
    fconstructor,
    fconstructor,
    tauto,
    tauto,
  },
  {
    intro p,
    intro q,
    split,
    {
      intro l,
      intro p₁,
      assume a₂,
      cases a₂,
      have c₁ : p = (t . (named x)) ∨ p ≠ (t . (named x)),
      tauto,
      cases c₁,
      {
        have c₂ : q = (t . (named y)) ∨ q ≠ (t . (named y)),
        tauto,
        cases c₂,
        {
          have h₁ : (t . (named x)).transition l p₁,
          subst c₁,
          exact a₂_right,
          have h₂ : l = t,
          exact ccs.transition_ap_a x p₁ t l h₁,
          have h₃ : (t . (named x)).transition t p₁ → p₁ = x,
          exact ccs.transtion_ap_only x p₁ t,
          have h₄ : p₁ = x,
          subst h₂,
          exact h₃ h₁,
          fconstructor,
          exact y,
          split,
          suffices s₁ : ccs.transition (t . (named y)) t y,
          subst h₂,
          subst c₂,
          exact s₁,
          exact ccs.transition_ap y t,
          suffices s₁ : s x y,
          subst h₄,
          exact s₁,
          exact relation.join_relations_right (relation.relation2 (t . x.named) (t . y.named)) 
            r x y a₁_h_left,
        },
        {
          have h₁ : s p q → (p = (t . x.named) ∧ q = (t . y.named)) ∨ r p q,
          exact (set.mem_union (p, q) (relation.conj_relation (relation.relation2 (t . x.named) 
            (t . y.named))) (relation.conj_relation r)).mp,
          have h₂ : (p = (t . x.named) ∧ q = (t . y.named)) ∨ r p q,
          exact h₁ a₂_left,
          have h₃ : r p q,
          tauto,
          have h₄ : r p q ∧ ccs.transition p l p₁,
          tauto,
          have h₅ : ∃ y₁, q.transition l y₁ ∧ r p₁ y₁,
          exact ccs.bisimilar_left r a₁_h_right p q l p₁ h₄,
          cases h₅,
          cases h₅_h,
          rename h₅_w q₁,
          fconstructor,
          exact q₁,
          split,
          tauto,
          exact relation.join_relations_right (relation.relation2 (t . x.named) (t . y.named)) 
            r p₁ q₁ h₅_h_right,
        },
      },
      {
        have h₁ : s p q → (p = (t . x.named) ∧ q = (t . y.named)) ∨ r p q,
        exact (set.mem_union (p, q) (relation.conj_relation (relation.relation2 (t . x.named) 
          (t . y.named))) (relation.conj_relation r)).mp,
        have h₂ : (p = (t . x.named) ∧ q = (t . y.named)) ∨ r p q,
        exact h₁ a₂_left,
        have h₃ : r p q,
        tauto,
        have h₄ : r p q ∧ ccs.transition p l p₁,
        tauto,
        have h₅ : ∃ y₁, q.transition l y₁ ∧ r p₁ y₁,
        exact ccs.bisimilar_left r a₁_h_right p q l p₁ h₄,
        cases h₅,
        cases h₅_h,
        rename h₅_w q₁,
        fconstructor,
        exact q₁,
        split,
        tauto,
        exact relation.join_relations_right (relation.relation2 (t . x.named) (t . y.named)) 
          r p₁ q₁ h₅_h_right,
      },
    },
    {
      intro l,
      intro q₁,
      assume a₂,
      cases a₂,
      have c₁ : p = (t . (named x)) ∨ p ≠ (t . (named x)),
      tauto,
      cases c₁,
      {
        have c₂ : q = (t . (named y)) ∨ q ≠ (t . (named y)),
        tauto,
        cases c₂,
        {
          have h₁ : (t . (named y)).transition l q₁,
          subst c₂,
          exact a₂_right,
          have h₂ : l = t,
          exact ccs.transition_ap_a y q₁ t l h₁,
          have h₃ : (t . (named y)).transition t q₁ → q₁ = y,
          exact ccs.transtion_ap_only y q₁ t,
          have h₄ : q₁ = y,
          subst h₂,
          exact h₃ h₁,
          fconstructor,
          exact x,
          split,
          suffices s₁ : ccs.transition (t . (named x)) t x,
          subst h₂,
          subst c₁,
          exact s₁,
          exact ccs.transition_ap x t,
          suffices s₁ : s x y,
          subst h₄,
          exact s₁,
          exact relation.join_relations_right (relation.relation2 (t . x.named) (t . y.named)) 
            r x y a₁_h_left,
        },
        {
          have h₁ : s p q → (p = (t . x.named) ∧ q = (t . y.named)) ∨ r p q,
          exact (set.mem_union (p, q) (relation.conj_relation (relation.relation2 (t . x.named) 
            (t . y.named))) (relation.conj_relation r)).mp,
          have h₂ : (p = (t . x.named) ∧ q = (t . y.named)) ∨ r p q,
          exact h₁ a₂_left,
          have h₃ : r p q,
          tauto,
          have h₄ : r p q ∧ ccs.transition q l q₁,
          tauto,
          have h₅ : ∃ y₁, p.transition l y₁ ∧ r y₁ q₁,
          exact ccs.bisimilar_right r a₁_h_right p q l q₁ h₄,
          cases h₅,
          cases h₅_h,
          rename h₅_w p₁,
          fconstructor,
          exact p₁,
          split,
          tauto,
          exact relation.join_relations_right (relation.relation2 (t . x.named) (t . y.named)) 
            r p₁ q₁ h₅_h_right,
        },
      },
      {
        have h₁ : s p q → (p = (t . x.named) ∧ q = (t . y.named)) ∨ r p q,
        exact (set.mem_union (p, q) (relation.conj_relation (relation.relation2 (t . x.named) 
          (t . y.named))) (relation.conj_relation r)).mp,
        have h₂ : (p = (t . x.named) ∧ q = (t . y.named)) ∨ r p q,
        exact h₁ a₂_left,
        have h₃ : r p q,
        tauto,
        have h₄ : r p q ∧ ccs.transition q l q₁,
        tauto,
        have h₅ : ∃ y₁, p.transition l y₁ ∧ r y₁ q₁,
        exact ccs.bisimilar_right r a₁_h_right p q l q₁ h₄,
        cases h₅,
        cases h₅_h,
        rename h₅_w p₁,
        fconstructor,
        exact p₁,
        split,
        tauto,
        exact relation.join_relations_right (relation.relation2 (t . x.named) (t . y.named)) 
          r p₁ q₁ h₅_h_right,
      },
    },
  },
end

lemma ccs.transition_psq_1 : ∀ (x a b x₁: ccs lab) (t : lab), ccs.funcion1 a b x ∧ ccs.transition x 
  t x₁ → ccs.transition a t x₁ ∨ ccs.transition b t x₁ :=
begin
  introv,
  assume a₁,
  cases a₁,
  have h₁ : ccs.funcion1 a b x → x = (a + b : ccs lab),
  tauto,
  have h₂ : x = (a + b : ccs lab),
  tauto,
  suffices s₁ : ccs.transition (a + b) t x₁ → ccs.transition a t x₁ ∨ ccs.transition b t x₁,
  subst h₂,
  exact s₁ a₁_right,
  assume a₂,
  cases a₂,
  {
    have h₃ : (a + b).or_transition a.named t x₁ → ccs.or_transition a a t x₁,
    tauto,
    have h₄ : ccs.or_transition a a t x₁,
    exact h₃ a₂,
    have h₅ : ccs.or_transition a a t x₁ → ccs.transition a t x₁,
    tauto,
    tauto,
  },
  {
    have h₃ : (a + b).or_transition b.named t x₁ → ccs.or_transition b b t x₁,
    tauto,
    have h₄ : ccs.or_transition b b t x₁,
    exact h₃ a₂,
    have h₅ : ccs.or_transition b b t x₁ → ccs.transition b t x₁,
    tauto,
    tauto,
  },
end

lemma ccs.transition_psq_2 : ∀ (x a b x₁: ccs lab) (t : lab), ccs.funcion2 a b x ∧ ccs.transition x 
  t x₁ → ccs.transition b t x₁ ∨ ccs.transition a t x₁ :=
begin
  introv,
  assume a₁,
  cases a₁,
  have h₁ : ccs.funcion1 a b x → x = (b + a : ccs lab),
  tauto,
  have h₂ : x = (b + a : ccs lab),
  tauto,
  suffices s₁ : ccs.transition (b + a) t x₁ → ccs.transition b t x₁ ∨ ccs.transition a t x₁,
  subst h₂,
  exact s₁ a₁_right,
  assume a₂,
  cases a₂,
  {
    have h₃ : (b + a).or_transition b.named t x₁ → ccs.or_transition b b t x₁,
    tauto,
    have h₄ : ccs.or_transition b b t x₁,
    exact h₃ a₂,
    have h₅ : ccs.or_transition b b t x₁ → ccs.transition b t x₁,
    tauto,
    tauto,
  },
  {
    have h₃ : (b + a).or_transition a.named t x₁ → ccs.or_transition a a t x₁,
    tauto,
    have h₄ : ccs.or_transition a a t x₁,
    exact h₃ a₂,
    have h₅ : ccs.or_transition a a t x₁ → ccs.transition a t x₁,
    tauto,
    tauto,
  },
end

lemma ccs.transition_psq_left : ∀ (x y z : ccs lab) (t : lab), ccs.transition x t z → 
  ccs.transition (x + y) t z :=
begin
  introv,
  assume a₁,
  fconstructor,
  have h₁ : x.transition t z → (x.named).transition t z,
  tauto,
  have h₂ : (x.named).transition t z,
  tauto,
  suffices s₁ : (x.named).or_transition x.named t z,
  tauto,
  tauto,
end

lemma ccs.transition_psq_right : ∀ (x y z : ccs lab) (t : lab), ccs.transition y t z → 
  ccs.transition (x + y) t z :=
begin
  introv,
  assume a₁,
  have h₁ : (y.named).transition t z,
  tauto,
  have h₂ : (y.named).or_transition y.named t z,
  tauto,
  have h₃ : (x + y).or_transition y.named t z,
  tauto,
  suffices s₁ : (x + y).or_transition x.named t z ∨ (x + y).or_transition y.named t z,
  tauto,
  tauto,
end

theorem ccs.property_psq_bisimilar : ∀ (x y z : ccs lab), x ∼ y → (x + z) ∼ (y + z) ∧ 
  (z + x) ∼ (z + y) := 
begin
  intro,
  intro,
  intro,
  assume a₁,
  cases a₁,
  cases a₁_h,
  rename a₁_w r,
  split,
  {
    let s := relation.join_relations (relation.relation4 r ccs.funcion1) 
      (relation.join_relations r relation.identity_relation),
    fconstructor,
    exact s,
    split,
    {
      fconstructor,
      fconstructor,
      exact x,
      fconstructor,
      exact y,
      fconstructor,
      exact z,
      split,
      fconstructor,
      split,
      fconstructor,
      exact a₁_h_left,
    },
    {
      intro q,
      intro w,
      split,
      {
        intro l,
        intro q₁,
        assume a₂,
        cases a₂,
        cases a₂_left,
        {
          cases a₂_left,
          cases a₂_left_h,
          cases a₂_left_h_h,
          rename a₂_left_w i,
          rename a₂_left_h_w j,
          rename a₂_left_h_h_w k,
          rename a₂_left_h_h_h a₂,
          cases a₂,
          cases a₂_right_1,
          have h₁ : ccs.funcion1 i k q ∧ ccs.transition q l q₁,
          tauto,
          have c₁ : ccs.transition i l q₁ ∨ ccs.transition k l q₁,
          exact ccs.transition_psq_1 q i k q₁ l h₁,
          cases c₁,
          {
            have h₂ : r i j ∧ ccs.transition i l q₁,
            tauto,
            have h₃ : ∃ (w₁ : ccs lab), (ccs.transition j l w₁ ∧ (r q₁ w₁)),
            exact ccs.bisimilar_left r a₁_h_right i j l q₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w w₁,
            fconstructor,
            exact w₁,
            split,
            {
              have h₄ : ccs.transition (j + k : ccs lab) l w₁,
              exact ccs.transition_psq_left j k w₁ l h₃_h_left,
              have h₅ : w = (j + k),
              tauto,
              subst h₅,
              exact h₄,
            },
            {
              suffices s₁ : relation.join_relations r relation.identity_relation q₁ w₁,
              exact relation.join_relations_right (relation.relation4 r ccs.funcion1) 
                (relation.join_relations r relation.identity_relation) q₁ w₁ s₁,
              fconstructor,
              tauto,
            },
          },
          {
            fconstructor,
            exact q₁,
            split,
            have h₂ : ccs.transition (j + k) l q₁,
            exact ccs.transition_psq_right j k q₁ l c₁,
            have h₃ : w = (j + k),
            tauto,
            subst h₃,
            exact h₂,
            suffices s₁ : relation.join_relations r relation.identity_relation q₁ q₁,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion1) 
              (relation.join_relations r relation.identity_relation) q₁ q₁ s₁,
            have h₄ : relation.identity_relation q₁ q₁,
            tauto,
            exact relation.join_relations_right r relation.identity_relation q₁ q₁ h₄,
          },
        },
        {
          cases a₂_left,
          {
            have h₁ : r q w,
            tauto,
            have h₂ : r q w ∧ ccs.transition q l q₁,
            tauto,
            have h₃ : ∃ (y₁ : ccs lab), w.transition l y₁ ∧ r q₁ y₁,
            exact ccs.bisimilar_left r a₁_h_right q w l q₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w w₁,
            fconstructor,
            exact w₁,
            split,
            tauto,
            have h₄ : relation.join_relations r relation.identity_relation q₁ w₁,
            fconstructor,
            tauto,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion1)
              (relation.join_relations r relation.identity_relation) q₁ w₁ h₄,
          },
          {
            have h₁ : q = w,
            tauto,
            fconstructor,
            exact q₁,
            split,
            subst h₁,
            exact a₂_right,
            have h₂ : relation.identity_relation q₁ q₁,
            tauto,
            have h₃ : relation.join_relations r relation.identity_relation q₁ q₁,
            exact relation.join_relations_right r relation.identity_relation q₁ q₁ h₂,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion1)
              (relation.join_relations r relation.identity_relation) q₁ q₁ h₃,
          },
        },
      },
      {
        intro l,
        intro w₁,
        assume a₂,
        cases a₂,
        cases a₂_left,
        {
          cases a₂_left,
          cases a₂_left_h,
          cases a₂_left_h_h,
          rename a₂_left_w i,
          rename a₂_left_h_w j,
          rename a₂_left_h_h_w k,
          rename a₂_left_h_h_h a₂,
          cases a₂,
          cases a₂_right_1,
          have h₁ : ccs.funcion1 j k w ∧ ccs.transition w l w₁,
          tauto,
          have c₁ : ccs.transition j l w₁ ∨ ccs.transition k l w₁,
          exact ccs.transition_psq_1 w j k w₁ l h₁,
          cases c₁,
          {
            have h₂ : r i j ∧ ccs.transition j l w₁,
            tauto,
            have h₃ : ∃ (q₁ : ccs lab), (ccs.transition i l q₁ ∧ (r q₁ w₁)),
            exact ccs.bisimilar_right r a₁_h_right i j l w₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w q₁,
            fconstructor,
            exact q₁,
            split,
            {
              have h₄ : ccs.transition (i + k : ccs lab) l q₁,
              exact ccs.transition_psq_left i k q₁ l h₃_h_left,
              have h₅ : q = (i + k),
              tauto,
              subst h₅,
              exact h₄,
            },
            {
              suffices s₁ : relation.join_relations r relation.identity_relation q₁ w₁,
              exact relation.join_relations_right (relation.relation4 r ccs.funcion1) 
                (relation.join_relations r relation.identity_relation) q₁ w₁ s₁,
              fconstructor,
              tauto,
            },
          },
          {
            fconstructor,
            exact w₁,
            split,
            have h₂ : ccs.transition (i + k) l w₁,
            exact ccs.transition_psq_right i k w₁ l c₁,
            have h₃ : q = (i + k),
            tauto,
            subst h₃,
            exact h₂,
            suffices s₁ : relation.join_relations r relation.identity_relation w₁ w₁,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion1) 
              (relation.join_relations r relation.identity_relation) w₁ w₁ s₁,
            have h₄ : relation.identity_relation w₁ w₁,
            tauto,
            exact relation.join_relations_right r relation.identity_relation w₁ w₁ h₄,
          },
        },
        {
          cases a₂_left,
          {
            have h₁ : r q w,
            tauto,
            have h₂ : r q w ∧ ccs.transition w l w₁,
            tauto,
            have h₃ : ∃ (y₁ : ccs lab), q.transition l y₁ ∧ r y₁ w₁,
            exact ccs.bisimilar_right r a₁_h_right q w l w₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w q₁,
            fconstructor,
            exact q₁,
            split,
            tauto,
            have h₄ : relation.join_relations r relation.identity_relation q₁ w₁,
            fconstructor,
            tauto,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion1)
              (relation.join_relations r relation.identity_relation) q₁ w₁ h₄,
          },
          {
            have h₁ : q = w,
            tauto,
            fconstructor,
            exact w₁,
            split,
            subst h₁,
            exact a₂_right,
            have h₂ : relation.identity_relation w₁ w₁,
            tauto,
            have h₃ : relation.join_relations r relation.identity_relation w₁ w₁,
            exact relation.join_relations_right r relation.identity_relation w₁ w₁ h₂,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion1)
              (relation.join_relations r relation.identity_relation) w₁ w₁ h₃,
          },
        },
      },
    },
  },
  {
    let s := relation.join_relations (relation.relation4 r ccs.funcion2) 
      (relation.join_relations r relation.identity_relation),
    fconstructor,
    exact s,
    split,
    {
      fconstructor,
      fconstructor,
      exact x,
      fconstructor,
      exact y,
      fconstructor,
      exact z,
      split,
      fconstructor,
      split,
      fconstructor,
      exact a₁_h_left,
    },
    {
      intro q,
      intro w,
      split,
      {
        intro l,
        intro q₁,
        assume a₂,
        cases a₂,
        cases a₂_left,
        {
          cases a₂_left,
          cases a₂_left_h,
          cases a₂_left_h_h,
          rename a₂_left_w i,
          rename a₂_left_h_w j,
          rename a₂_left_h_h_w k,
          rename a₂_left_h_h_h a₂,
          cases a₂,
          cases a₂_right_1,
          have h₁ : ccs.funcion2 i k q ∧ ccs.transition q l q₁,
          tauto,
          have c₁ : ccs.transition k l q₁ ∨ ccs.transition i l q₁,
          exact ccs.transition_psq_2 q i k q₁ l h₁,
          cases c₁,
          {
            fconstructor,
            exact q₁,
            split,
            have h₂ : ccs.transition (k + j) l q₁,
            exact ccs.transition_psq_left k j q₁ l c₁,
            have h₃ : w = (k + j),
            tauto,
            subst h₃,
            exact h₂,
            suffices s₁ : relation.join_relations r relation.identity_relation q₁ q₁,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion2) 
              (relation.join_relations r relation.identity_relation) q₁ q₁ s₁,
            have h₄ : relation.identity_relation q₁ q₁,
            tauto,
            exact relation.join_relations_right r relation.identity_relation q₁ q₁ h₄,
          },
          {
            have h₂ : r i j ∧ ccs.transition i l q₁,
            tauto,
            have h₃ : ∃ (w₁ : ccs lab), (ccs.transition j l w₁ ∧ (r q₁ w₁)),
            exact ccs.bisimilar_left r a₁_h_right i j l q₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w w₁,
            fconstructor,
            exact w₁,
            split,
            {
              have h₄ : ccs.transition (k + j : ccs lab) l w₁,
              exact ccs.transition_psq_right k j w₁ l h₃_h_left,
              have h₅ : w = (k + j),
              tauto,
              subst h₅,
              exact h₄,
            },
            {
              suffices s₁ : relation.join_relations r relation.identity_relation q₁ w₁,
              exact relation.join_relations_right (relation.relation4 r ccs.funcion2) 
                (relation.join_relations r relation.identity_relation) q₁ w₁ s₁,
              fconstructor,
              tauto,
            },
          },
        },
        {
          cases a₂_left,
          {
            have h₁ : r q w,
            tauto,
            have h₂ : r q w ∧ ccs.transition q l q₁,
            tauto,
            have h₃ : ∃ (y₁ : ccs lab), w.transition l y₁ ∧ r q₁ y₁,
            exact ccs.bisimilar_left r a₁_h_right q w l q₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w w₁,
            fconstructor,
            exact w₁,
            split,
            tauto,
            have h₄ : relation.join_relations r relation.identity_relation q₁ w₁,
            fconstructor,
            tauto,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion2)
              (relation.join_relations r relation.identity_relation) q₁ w₁ h₄,
          },
          {
            have h₁ : q = w,
            tauto,
            fconstructor,
            exact q₁,
            split,
            subst h₁,
            exact a₂_right,
            have h₂ : relation.identity_relation q₁ q₁,
            tauto,
            have h₃ : relation.join_relations r relation.identity_relation q₁ q₁,
            exact relation.join_relations_right r relation.identity_relation q₁ q₁ h₂,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion2)
              (relation.join_relations r relation.identity_relation) q₁ q₁ h₃,
          },
        },
      },
      {
        intro l,
        intro w₁,
        assume a₂,
        cases a₂,
        cases a₂_left,
        {
          cases a₂_left,
          cases a₂_left_h,
          cases a₂_left_h_h,
          rename a₂_left_w i,
          rename a₂_left_h_w j,
          rename a₂_left_h_h_w k,
          rename a₂_left_h_h_h a₂,
          cases a₂,
          cases a₂_right_1,
          have h₁ : ccs.funcion2 j k w ∧ ccs.transition w l w₁,
          tauto,
          have c₁ : ccs.transition k l w₁ ∨ ccs.transition j l w₁,
          exact ccs.transition_psq_2 w j k w₁ l h₁,
          cases c₁,
          {
            fconstructor,
            exact w₁,
            split,
            have h₂ : ccs.transition (k + i) l w₁,
            exact ccs.transition_psq_left k i w₁ l c₁,
            have h₃ : q = (k + i),
            tauto,
            subst h₃,
            exact h₂,
            suffices s₁ : relation.join_relations r relation.identity_relation w₁ w₁,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion2) 
              (relation.join_relations r relation.identity_relation) w₁ w₁ s₁,
            have h₄ : relation.identity_relation w₁ w₁,
            tauto,
            exact relation.join_relations_right r relation.identity_relation w₁ w₁ h₄,
          },
          {
            have h₂ : r i j ∧ ccs.transition j l w₁,
            tauto,
            have h₃ : ∃ (q₁ : ccs lab), (ccs.transition i l q₁ ∧ (r q₁ w₁)),
            exact ccs.bisimilar_right r a₁_h_right i j l w₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w q₁,
            fconstructor,
            exact q₁,
            split,
            {
              have h₄ : ccs.transition (k + i : ccs lab) l q₁,
              exact ccs.transition_psq_right k i q₁ l h₃_h_left,
              have h₅ : q = (k + i),
              tauto,
              subst h₅,
              exact h₄,
            },
            {
              suffices s₁ : relation.join_relations r relation.identity_relation q₁ w₁,
              exact relation.join_relations_right (relation.relation4 r ccs.funcion2) 
                (relation.join_relations r relation.identity_relation) q₁ w₁ s₁,
              fconstructor,
              tauto,
            },
          },
        },
        {
          cases a₂_left,
          {
            have h₁ : r q w,
            tauto,
            have h₂ : r q w ∧ ccs.transition w l w₁,
            tauto,
            have h₃ : ∃ (y₁ : ccs lab), q.transition l y₁ ∧ r y₁ w₁,
            exact ccs.bisimilar_right r a₁_h_right q w l w₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w q₁,
            fconstructor,
            exact q₁,
            split,
            tauto,
            have h₄ : relation.join_relations r relation.identity_relation q₁ w₁,
            fconstructor,
            tauto,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion2)
              (relation.join_relations r relation.identity_relation) q₁ w₁ h₄,
          },
          {
            have h₁ : q = w,
            tauto,
            fconstructor,
            exact w₁,
            split,
            subst h₁,
            exact a₂_right,
            have h₂ : relation.identity_relation w₁ w₁,
            tauto,
            have h₃ : relation.join_relations r relation.identity_relation w₁ w₁,
            exact relation.join_relations_right r relation.identity_relation w₁ w₁ h₂,
            exact relation.join_relations_right (relation.relation4 r ccs.funcion2)
              (relation.join_relations r relation.identity_relation) w₁ w₁ h₃,
          },
        },
      },
    }
  },
end

lemma ccs.transition_pq_left : ∀ (x y z : ccs lab) (l : lab), (∃ c, x.transition
  l c ∧ z = (ccs.pq c y.named)) → ccs.transition (x ∣ y) l z := 
begin
  introv,
  assume a,
  fconstructor,
  tauto,
end

lemma ccs.transition_pq_mid : ∀ (x y z : ccs lab) (l : lab), (∃ c, y.transition l c ∧ z = 
  (ccs.pq x.named c)) → ccs.transition (x ∣ y) l z := 
begin
  introv,
  assume a,
  cases a,
  rename a_w c,
  cases a_h,
  have h₁ : (y.named).transition l c,
  tauto,
  have h₂ : (y.named).or_transition y.named l c,
  tauto,
  have h₃ : (x ∣ y).or_transition y.named l c,
  tauto,
  suffices s₁ : (∃ c, ccs.or_transition (x ∣ y) x.named l c ∧ z = (pq c y.named)) ∨ (∃ c, 
    ccs.or_transition (x ∣ y) y.named l c ∧ z = (pq x.named c)) ∨ (∃ c d, ccs.or_transition (x ∣ y)
    x.named l c ∧ ccs.or_transition (x ∣ y) y.named l d ∧ z = (pq c d)),
  tauto,
  suffices s₁ : (∃ c, ccs.or_transition (x ∣ y) y.named l c ∧ z = (pq x.named c)),
  itauto,
  fconstructor,
  exact c,
  split,
  exact h₃,
  exact a_h_right,
end

lemma ccs.transition_pq_right : ∀ (x y z : ccs lab) (l : lab), (∃ c d , x.transition l c ∧ 
  y.transition l d ∧ z = (ccs.pq c d)) → ccs.transition (x ∣ y) l z := 
begin
  introv,
  assume a,
  cases a,
  cases a_h,
  suffices s₁ : (∃ c, ccs.or_transition (x ∣ y) x.named l c ∧ z = (pq c y.named)) ∨ (∃ c, 
    ccs.or_transition (x ∣ y) y.named l c ∧ z = (pq x.named c)) ∨ (∃ c d, ccs.or_transition (x ∣ y)
    x.named l c ∧ ccs.or_transition (x ∣ y) y.named l d ∧ z = (pq c d)),
  tauto,
  suffices s₂ : (∃ c d, ccs.or_transition (x ∣ y)
    x.named l c ∧ ccs.or_transition (x ∣ y) y.named l d ∧ z = (pq c d)),
  tauto,
  rename a_w c,
  rename a_h_w d,
  fconstructor,
  exact c,
  fconstructor,
  exact d,
  split,
  tauto,
  split,
  tauto,
  tauto,
end

lemma ccs.transition_pq : ∀ (i j z : ccs lab) (t : lab), (i ∣ j).transition t z → ∃ (k l : ccs lab), 
  z = (k.pq l) :=
begin
  introv,
  assume a,
  cases a,
  {
    cases a,
    cases a_h,
    fconstructor,
    exact a_w,
    fconstructor,
    exact j,
    tauto,
  },
  {
    cases a,
    {
      cases a,
      cases a_h,
      fconstructor,
      exact i,
      fconstructor,
      exact a_w,
      tauto,
    },
    {
      cases a,
      cases a_h,
      cases a_h_h,
      cases a_h_h_right,
      fconstructor,
      exact a_w,
      fconstructor,
      exact a_h_w,
      tauto,
    },
  },
end

theorem ccs.property_pq_bisimilar : ∀ (x y z : ccs lab), x ∼ y → (x ∣ z) ∼ (y ∣ z) ∧ 
  (z ∣ x) ∼ (z ∣ y) := 
begin
  introv,
  assume a₁,
  cases a₁,
  rename a₁_w r,
  split,
  {
    let s : ccs lab → ccs lab → Prop := ccs.relation1,
    fconstructor,
    exact s,
    split,
    fconstructor,
    fconstructor,
    exact r,
    exact a₁_h,
    tauto,
    intro q,
    intro w,
    split,
    {
      intro l,
      intro q₁,
      assume a₂,
      cases a₂,
      
    },
    {
      sorry,
    },
  },
  {
    sorry,
  },
end