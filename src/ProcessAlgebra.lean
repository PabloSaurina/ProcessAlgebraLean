import data.fintype.basic
import data.pfun
import logic.function.iterate
import order.basic
import tactic.apply_fun
import set_theory.cardinal
import data.fin.tuple

universes u v

namespace ProcessAlgebra


-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
--                                      LTS
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------


structure LTS (proc: Type u) (act: Type v) := 
  (start: proc)
  (f: proc → act → set proc)

namespace LTS

variables {proc: Type u} {act: Type v}
  (P : LTS proc act)

-- Primero definimos una funcion para juntar LTS

def union_fun (f g : proc → act → set proc) : proc → act → set proc
|p a := set.union (f p a) (g p a)

def union_lts (P Q : LTS proc act) : LTS proc act :=
LTS.mk P.start (union_fun  P.f Q.f)

-- Definimos las transiciones

def transition: proc → act → set proc
|p a:=(P.f p a)

def exist_transition_from: proc → proc → Prop
|p q:= ∃ a, (q ∈ P.f p a)

def reaches_from: proc → proc → Prop :=
  relation.refl_trans_gen (λ a b, P.exist_transition_from a b)

def reaches: proc → Prop
|q := P.reaches_from P.start q

-- Definimos la bisimilitud fuerte

def bisimulation (r : proc → proc → Prop):= ∀ p q, (∀ a (p₁:proc), 
  (r p q ∧ p₁ ∈ P.transition p a) → ∃ (q₁:proc), (q₁ ∈ P.transition q a 
  ∧ (r p₁ q₁))) ∧ (∀ b (q₁:proc), (r p q ∧ q₁ ∈ P.transition q b) → ∃ 
  (p₁:proc), (p₁ ∈ P.transition p b ∧ (r p₁ q₁)))

def bisimilar (p q : proc) :=
  ∃ (s : proc → proc → Prop), (s p q) ∧ P.bisimulation s

def strong_bisimilarity: proc → proc → Prop
|p q := P.bisimilar p q

-- Le asignamos la notacion usual

infix ` ∼ `:40 := LTS.strong_bisimilarity

end LTS 

-- Para las proximas demostraciones utilizaremos ciertas relaciones 
-- que hay que definir previamente. Realizamos esto dentro del espacio 
-- 'relation'

namespace relation

variable {X: Type u}

def inverted_binary_relation (r:X → X → Prop) : X → X → Prop
|q p := r p q

def identity_relation : X → X → Prop
|q p := p = q

def relation1 (r:X → X → Prop) (s:X → X → Prop) : 
  X → X → Prop 
|a b := ∃ c, r a c ∧ s c b

def relation2 (x:X) (y:X) : X → X → Prop
|a b := (a = x ∧ b = y)

def relation3 (r:X → X → Prop) (s:X → X → Prop) : X → X → Prop 
|a b := r a b ∨ s a b

def relation4 (r:X → X → Prop) (f:X → X → X → Prop) : X → X → Prop
|a b := ∃ (x y z : X), f x z a ∧ f y z b ∧ r x y

def conj_relation (r:X → X → Prop) : (set (X × X))
|(a,b) := r a b

def relation_conj (A : set (X × X)) : X → X → Prop
|a b := (a,b)∈ A

def join_relations (r:X → X → Prop) (s:X → X → Prop) : X → X → Prop
|a b := relation_conj (set.union (conj_relation r) (conj_relation s)) a b

end relation


-- Probamos ciertos reusltados sencillos

variables {proc act : Type u}

lemma lts.bisimulation.identity_relation : ∀ (P:LTS proc act),
  P.bisimulation relation.identity_relation :=
begin
  intro P,
  intro x,
  intro y,
  split,
  {
    intro t,
    intro z,
    assume h,
    cases h,
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
    intro t,
    intro z,
    assume h,
    cases h,
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

lemma lts.bisimilar.symmetric:  ∀ (P₁: LTS proc act), symmetric (P₁.bisimilar) :=
begin
  intro P,
  intro x,
  intro y,
  assume a₁,
  have h₁ : ∃ (r : proc  → proc  → Prop), (r x y) ∧ P.bisimulation r,
  from a₁,
  cases h₁,
  let r₁ := relation.inverted_binary_relation h₁_w,
  suffices h₂ : ∃ (r : proc  → proc  → Prop), (r y x) ∧ P.bisimulation r,
  from h₂,
  suffices h₃ : (r₁ y x) ∧ P.bisimulation r₁,
  split,
  from h₃,
  cases h₁_h,
  split,
  from h₁_h_left,
  have s₂ : ∀ x y, (∀ a (x₁ : proc), (h₁_w x y ∧ x₁ ∈ 
    P.transition x a) → ∃ (y₁ : proc), (y₁ ∈ P.transition y a 
    ∧ (h₁_w x₁ y₁))) ∧ (∀ b (y₁ : proc), (h₁_w x y ∧ y₁ ∈ 
    P.transition y b) → ∃ (x₁ : proc), (x₁ ∈ P.transition x b
    ∧ (h₁_w x₁ y₁))),
  from h₁_h_right,
  intro w,
  intro z,
  have s₃ : (∀ t (z₁ : proc), (h₁_w z w ∧ z₁ ∈ P.transition 
    z t) → ∃ (w₁ : proc), (w₁ ∈ P.transition w t ∧ (h₁_w z₁ w₁))) 
    ∧ (∀ t (w₁ : proc), (h₁_w z w ∧ w₁ ∈ P.transition w t) → ∃ 
    (z₁ : proc), (z₁ ∈ P.transition z t ∧ (h₁_w z₁ w₁))),
  from s₂ z w,
  cases s₃,
  split,
  {
    intro t,
    intro w₁,
    assume h₂,
    have s₄ : h₁_w z w ∧ w₁ ∈ P.transition w t,
    from h₂,
    have s₅ : h₁_w z w ∧ w₁ ∈ P.transition w t → 
      (∃ (z₁ : proc), z₁ ∈ P.transition z t ∧ h₁_w z₁ w₁),
    from s₃_right t w₁,
    have s₆ : (∃ (z₁ : proc), z₁ ∈ P.transition z t 
      ∧ h₁_w z₁ w₁),
    from s₅ s₄,
    cases s₆,
    rename s₆_w z₁,
    have h₃ : z₁ ∈ P.transition z t ∧ r₁ w₁ z₁,
    from s₆_h,
    split,
    from h₃,
  },
  {
    intro t,
    intro z₁,
    assume h₂,
    have s₄ : h₁_w z w ∧ z₁ ∈ P.transition z t,
    from h₂,
    have s₅ : h₁_w z w ∧ z₁ ∈ P.transition z t → 
      (∃ (w₁ : proc), w₁ ∈ P.transition w t ∧ h₁_w z₁ w₁),
    from s₃_left t z₁,
    have s₆ : (∃ (w₁ : proc), w₁ ∈ P.transition w t 
      ∧ h₁_w z₁ w₁),
    from s₅ s₄,
    cases s₆,
    rename s₆_w w₁,
    have h₃ : w₁ ∈ P.transition w t ∧ r₁ w₁ z₁,
    from s₆_h,
    split,
    from h₃,
  },
end

lemma lts.bisimilar.reflexive: ∀ (P₁: LTS proc act), reflexive 
  (P₁.bisimilar) :=
begin
  intro,
  let r : (proc → proc → Prop) := relation.identity_relation,
  intro,
  fconstructor,
  exact r,
  split,
  fconstructor,
  exact lts.bisimulation.identity_relation P₁,
end

lemma lts.bisimilar_left: ∀ (P₁: LTS proc act), ∀ (r : proc → proc → 
  Prop), P₁.bisimulation r → ∀ x y, (∀ (a : act) (x₁ : proc), (r x y ∧ 
  P₁.transition x a x₁) → ∃ (y₁ : proc), (P₁.transition y a y₁ ∧ 
  (r x₁ y₁))) :=
begin
  intro,
  intro,
  assume a₁,
  intro,
  intro,
  have h₁ : (∀ (a : act) (x₁ : proc), (r x y ∧ P₁.transition x a x₁) → 
    ∃ (y₁ : proc), (P₁.transition y a y₁ ∧ (r x₁ y₁))) ∧ (∀ (b : act) 
    (y₁ : proc), (r x y ∧ P₁.transition y b y₁) → ∃ (x₁ : proc), 
    (P₁.transition x b x₁ ∧ (r x₁ y₁))),
  from a₁ x y,
  cases h₁,
  exact h₁_left,
end

lemma lts.bisimilar_right: ∀ (P₁: LTS proc act), ∀ (r : proc → proc → 
  Prop), P₁.bisimulation r → ∀ x y, (∀ (a : act) (y₁ : proc), (r x y ∧ 
  P₁.transition y a y₁) → ∃ (x₁ : proc), (P₁.transition x a x₁ ∧ 
  (r x₁ y₁))) :=
begin
  intro,
  intro,
  assume a₁,
  intro,
  intro,
  have h₁ : (∀ (a : act) (x₁ : proc), (r x y ∧ P₁.transition x a x₁) → 
    ∃ (y₁ : proc), (P₁.transition y a y₁ ∧ (r x₁ y₁))) ∧ (∀ (b : act) 
    (y₁ : proc), (r x y ∧ P₁.transition y b y₁) → ∃ (x₁ : proc), 
    (P₁.transition x b x₁ ∧ (r x₁ y₁))),
  from a₁ x y,
  cases h₁,
  exact h₁_right,
end


lemma lts.bisimilar.transitive: ∀ (P₁: LTS proc act), transitive 
  (P₁.bisimilar) :=
begin
  intro,
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
      have h₁ : ∃ (e : proc), r₁ q e ∧ r₂ e w,
      tauto,
      cases h₁,
      rename h₁_w e,
      have h₂ : ∀ x y, (∀ (a : act) (x₁ : proc), (r₁ x y ∧ P₁.transition 
        x a x₁) → ∃ (y₁ : proc), (P₁.transition y a y₁ ∧ (r₁ x₁ y₁))),
      exact lts.bisimilar_left P₁ r₁ a₁_h_right,
      have h₃ : ∃ (e₁ : proc), P₁.transition e t e₁ ∧ r₁ q₁ e₁,
      have h₄ : r₁ q e ∧ P₁.transition q t q₁,
      tauto,
      from h₂ q e t q₁ h₄,
      cases h₃,
      rename h₃_w e₁,
      have h₅ : ∀ x y, (∀ (a : act) (x₁ : proc), (r₂ x y ∧ P₁.transition 
        x a x₁) → ∃ (y₁ : proc), (P₁.transition y a y₁ ∧ (r₂ x₁ y₁))),
      exact lts.bisimilar_left P₁ r₂ a₂_h_right,
      have h₆ : ∃ (w₁ : proc), P₁.transition w t w₁ ∧ r₂ e₁ w₁,
      have h₇ : r₂ e w ∧ P₁.transition e t e₁,
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
      have h₁ : ∃ (e : proc), r₁ q e ∧ r₂ e w,
      tauto,
      cases h₁,
      rename h₁_w e,
      have h₂ : ∀ x y, (∀ (a : act) (y₁ : proc), (r₂ x y ∧ P₁.transition y 
        a y₁) → ∃ (x₁ : proc), (P₁.transition x a x₁ ∧ (r₂ x₁ y₁))),
      exact lts.bisimilar_right P₁ r₂ a₂_h_right,
      have h₃ : ∃ (e₁ : proc), P₁.transition e t e₁ ∧ r₂ e₁ w₁,
      have h₄ : r₂ e w ∧ P₁.transition w t w₁,
      tauto,
      from h₂ e w t w₁ h₄,
      cases h₃,
      rename h₃_w e₁,
      have h₅ : ∀ x y, (∀ (a : act) (y₁ : proc), (r₁ x y ∧ P₁.transition y 
        a y₁) → ∃ (x₁ : proc), (P₁.transition x a x₁ ∧ (r₁ x₁ y₁))),
      exact lts.bisimilar_right P₁ r₁ a₁_h_right,
      have h₆ : ∃ (q₁ : proc), P₁.transition q t q₁ ∧ r₁ q₁ e₁,
      have h₇ : r₁ q e ∧ P₁.transition e t e₁,
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

theorem lts.bismilar_relation.equivalence: ∀ (P₁: LTS proc act), 
  equivalence (P₁.strong_bisimilarity) :=
begin
  intro,
  split,
  {
    intro,
    suffices s₁ : P₁.bisimilar x x,
    tauto,
    have h₁ : reflexive P₁.bisimilar → P₁.bisimilar x x,
    tauto,
    exact h₁ (lts.bisimilar.reflexive P₁),
  },
  {
    split,
    {
      intro,
      intro,
      assume a₁,
      suffices s₁ : P₁.bisimilar y x,
      tauto,
      have h₁ : P₁.bisimilar x y,
      tauto,
      have h₂ : symmetric P₁.bisimilar → (P₁.bisimilar x y → P₁.bisimilar 
        y x),
      tauto,
      exact h₂ (lts.bisimilar.symmetric P₁) h₁,
    },
    {
      intro,
      intro,
      intro,
      assume a₁,
      assume a₂,
      have h₁ : P₁.bisimilar x y,
      tauto,
      have h₂ : P₁.bisimilar y z,
      tauto,
      suffices s₁ : P₁.bisimilar x z,
      tauto,
      have h₃ : transitive P₁.bisimilar → (P₁.bisimilar x y ∧ P₁.bisimilar 
        y z → P₁.bisimilar x z),
      tauto,
      have h₄ : P₁.bisimilar x y ∧ P₁.bisimilar y z,
      tauto,
      exact h₃ (lts.bisimilar.transitive P₁) h₄,
    },
  },
end

theorem lts.strong_bisimilarity.is_bisimulation : ∀ (P: LTS proc act), 
  P.bisimulation P.strong_bisimilarity :=
begin
  intro P,
  let r := P.strong_bisimilarity,
  suffices s₁ : P.bisimulation r,
  {
    from s₁,
  },
  {
    intro x,
    intro y,
    split,
    {
      intro t,
      intro z,
      assume s₁,
      cases s₁,
      rename s₁_left s₁,
      rename s₁_right s₂,
      have s₃ : P.bisimilar x y,
      {
        from s₁,
      },
      {
        have s₄ : ∃ (s : proc → proc → Prop), s x y ∧ P.bisimulation s,
        {
          from s₃,
        },
        {
          cases s₄,
          rename s₄_w s,
          cases s₄_h,
          suffices s₅ : ∃ (y₁ : proc), y₁ ∈ P.transition y t ∧ s z y₁,
          {
            cases s₅,
            rename s₅_w w,
            cases s₅_h,
            fconstructor,
            exact w,
            split,
            from s₅_h_left,
            fconstructor,
            exact s,
            split,
            from s₅_h_right,
            from s₄_h_right,
          },
          {
            have s₅ : (∀ a (x₁ : proc), (s x y ∧ x₁ ∈ P.transition x a) →
              ∃ (y₁ : proc), (y₁ ∈ P.transition y a ∧ (s x₁ y₁))) ∧ (∀ b 
              (y₁ : proc), (s x y ∧ y₁ ∈ P.transition y b) → ∃ (x₁ : proc), 
              (x₁ ∈ P.transition x b ∧ (s x₁ y₁))),
            from s₄_h_right x y,
            cases s₅,
            have s₆ : s x y ∧ z ∈ P.transition x t → (∃ (y₁ : proc),
              y₁ ∈ P.transition y t ∧ s z y₁),
            from s₅_left t z,
            itauto,
          },
        },
      },
    },
    {
      intro t,
      intro w,
      assume s₁,
      cases s₁,
      rename s₁_left s₁,
      rename s₁_right s₂,
      have s₃ : P.bisimilar x y,
      {
        from s₁,
      },
      {
        have s₄ : ∃ (s : proc → proc → Prop), s x y ∧ P.bisimulation s,
        {
          from s₃,
        },
        {
          cases s₄,
          rename s₄_w s,
          cases s₄_h,
          suffices s₅ : ∃ (y₁ : proc), y₁ ∈ P.transition x t ∧ s y₁ w,
          {
            cases s₅,
            rename s₅_w z,
            cases s₅_h,
            fconstructor,
            exact z,
            split,
            from s₅_h_left,
            fconstructor,
            exact s,
            tauto,
          },
          {
            have s₅ : (∀ a (x₁ : proc), (s x y ∧ x₁ ∈ P.transition x a) → 
              ∃ (y₁ : proc), (y₁ ∈ P.transition y a ∧ (s x₁ y₁))) ∧ (∀ b 
              (y₁ : proc), (s x y ∧ y₁ ∈ P.transition y b) → ∃ (x₁ : proc), 
              (x₁ ∈ P.transition x b ∧ (s x₁ y₁))),
            from s₄_h_right x y,
            cases s₅,
            have s₆ : s x y ∧ w ∈ P.transition y t → (∃ (y₁ : proc),
            y₁ ∈ P.transition x t ∧ s y₁ w),
            from s₅_right t w,
            itauto,
          },
        },
      },
    },
  },
end

lemma lts.strong_bisimilarity.supset.bisimulation : ∀ (P:LTS proc act), ∀ 
  (r:proc → proc → Prop), P.bisimulation r → (∀ x y, r x y → 
  P.strong_bisimilarity x y) :=
begin
  intro P,
  intro r,
  assume s₁,
  intro x,
  intro y,
  assume s₂,
  fconstructor,
  exact r,
  tauto,
end

theorem lts.strong_bisimilarity.is_largest_bisimulation : ∀ (P₁: LTS proc 
  act) (r₁:proc → proc → Prop), P₁.bisimulation r₁ → (cardinal.mk 
  (relation.conj_relation P₁.strong_bisimilarity)) >= (cardinal.mk 
  (relation.conj_relation r₁)) :=
begin
  intro P,
  let r := P.strong_bisimilarity,
  intro s,
  assume h₁,
  let cr := relation.conj_relation r,
  let cs := relation.conj_relation s,
  have h₂ : cs ⊆ cr,
  {
    intro a,
    assume h₂,
    cases a,
    rename a_fst a,
    rename a_snd b,
    suffices s₁ : s a b,
    {
      have h₃ : r a b,
      {
        have h₄ : P.bisimilar a b,
        {
          fconstructor,
          exact s,
          split,
          from s₁,
          from h₁,
        },
        {
          from h₄,
        },
      },
      {
        from h₃,
      },
    },
    {
      from h₂,
    },
  },
  {
    norm_num,
    have h : ∃f : cs → cr, function.injective f,
    {
      suffices s₁ : ∀ a ∈ cs, a ∈ cr,
      {
        let f: cs → cr := set.inclusion h₂,
        fconstructor,
        exact f,
        from set.inclusion_injective h₂,
      },
      {
        tauto,
      },
    },
    {
      cases h,
      from cardinal.mk_le_of_injective h_h,
    },
  },
end

theorem lts.strong_bisimilarity.nat_rec_decomp_bisimilarity : ∀ (P : LTS 
  proc act) (x y : proc), ( ( ∀ (t : act) (x₁ : proc), x₁ ∈ P.transition 
  x t → ∃ (y₁ : proc), y₁ ∈ P.transition y t ∧ P.strong_bisimilarity x₁ 
  y₁ ) ∧ ( ∀ (t : act) (y₁ : proc), y₁ ∈ P.transition y t → ∃ (x₁ : proc), 
  x₁ ∈ P.transition x t ∧ P.strong_bisimilarity x₁ y₁ ) ) → 
  P.strong_bisimilarity x y :=
begin 
  intro P,
  intro x,
  intro y,
  assume s₁,
  cases s₁,
  let r := relation.join_relations (relation.relation2 x y) 
    P.strong_bisimilarity,
  let con_r := (set.union (relation.conj_relation (relation.relation2 x y)) 
    (relation.conj_relation P.strong_bisimilarity)),
  suffices s₂ : P.bisimulation r,
  {
    have s₃ : r x y,
    {
      fconstructor,
      split,
      trivial,
      trivial,
    },
    {
      from lts.strong_bisimilarity.supset.bisimulation P r s₂ x y s₃,
    },
  },
  {
    intro a,
    intro b,
    split,
    {
      intro t,
      intro a₁,
      assume s₂,
      cases s₂,
      have c₁ : a = x ∨ a ≠ x,
      tauto,
      cases c₁,
      have c₂ : b = x ∨ b = y ∨ (b≠x ∧ b≠y),
      tauto,
      cases c₂,
      fconstructor,
      exact a₁,
      split,
      subst c₁,
      subst c₂,
      from s₂_right,
      have h : P.strong_bisimilarity a₁ a₁,
      fconstructor,
      exact relation.identity_relation,
      split,
      tauto,
      from lts.bisimulation.identity_relation P,
      suffices h₁ : (a₁,a₁) ∈ con_r,
      tauto,
      suffices h₂ : (a₁,a₁)∈ (relation.conj_relation P.strong_bisimilarity),
      exact (relation.conj_relation 
        (relation.relation2 x y)).mem_union_right h,
      fconstructor,
      exact relation.identity_relation,
      split,
      tauto,
      from lts.bisimulation.identity_relation P,
      cases c₂,
      have h : ∃(b₁ : proc), b₁ ∈ P.transition y t ∧ P.strong_bisimilarity 
        a₁ b₁,
      have h₁ : a₁ ∈ P.transition x t,
      subst c₁,
      from s₂_right,
      from s₁_left t a₁ h₁,
      cases h,
      fconstructor,
      exact h_w,
      cases h_h,
      split,
      subst c₂,
      from h_h_left,
      exact (relation.conj_relation 
        (relation.relation2 x y)).mem_union_right h_h_right,
      cases c₂,
      suffices h : (a,b) ∈ (relation.conj_relation P.strong_bisimilarity),
      have h₁ : P.strong_bisimilarity a b,
      tauto,
      have h₂ : ∃ (s : proc → proc → Prop), (s a b) ∧ P.bisimulation s,
      from h₁,
      cases h₂,
      rename h₂_w s,
      cases h₂_h,
      have h₃ : (∀ t (a₁ : proc), (s a b ∧ a₁ ∈ P.transition a t) → ∃ 
        (y₁ : proc), (y₁ ∈ P.transition b t ∧ (s a₁ y₁))) ∧ (∀ t (y₁ : 
        proc), (s a b ∧ y₁ ∈ P.transition b t) → ∃ (a₁ : proc), (a₁ ∈ 
        P.transition a t ∧ (s a₁ y₁))),
      from h₂_h_right a b,
      cases h₃,
      have h₄ : s a b ∧ a₁ ∈ P.transition a t,
      split,
      from h₂_h_left,
      from s₂_right,
      have h₅ : ∃ (y₁ : proc), y₁ ∈ P.transition b t ∧ s a₁ y₁,
      from h₃_left t a₁ h₄,
      cases h₅,
      rename h₅_w b₁,
      fconstructor,
      exact b₁,
      split,
      tauto,
      have h₆ : P.bisimilar a₁ b₁,
      fconstructor,
      exact s,
      tauto,
      exact (relation.conj_relation 
        (relation.relation2 x y)).mem_union_right h₆,
      have h₁ : P.strong_bisimilarity a b,
      have h₂ : r a b → (a = x ∧ b = y) ∨ P.strong_bisimilarity a b,
      exact (set.mem_union (a, b) (relation.conj_relation 
        (relation.relation2 x y)) (relation.conj_relation 
        (LTS.strong_bisimilarity P))).mp,
      have h₃ : (a = x ∧ b = y) ∨ P.strong_bisimilarity a b,
      from h₂ s₂_left,
      tauto,
      from h₁,
      have h₁ : r a b → (a = x ∧ b = y) ∨ P.strong_bisimilarity a b,
      exact (set.mem_union (a, b) 
        (relation.conj_relation (relation.relation2 x y)) 
        (relation.conj_relation (LTS.strong_bisimilarity P))).mp,
      have h₂ : (a = x ∧ b = y) ∨ P.strong_bisimilarity a b,
      from h₁ s₂_left,
      have h₃ : P.strong_bisimilarity a b,
      tauto,
      have h₄ : ∃ (s : proc → proc → Prop), (s a b) ∧ P.bisimulation s,
      from h₃,
      cases h₄,
      rename h₄_w s,
      cases h₄_h,
      have h₅ : (∀ t (a₁ : proc), (s a b ∧ a₁ ∈ P.transition a t) → ∃ (y₁ : 
        proc), (y₁ ∈ P.transition b t ∧ (s a₁ y₁))) ∧ (∀ t (y₁ : proc), 
        (s a b ∧ y₁ ∈ P.transition b t) → ∃ (a₁ : proc), (a₁ ∈ P.transition 
        a t ∧ (s a₁ y₁))),
      from h₄_h_right a b,
      cases h₅,
      have h₆ : s a b ∧ a₁ ∈ P.transition a t,
      split,
      from h₄_h_left,
      from s₂_right,
      have h₇ : ∃ (y₁ : proc), y₁ ∈ P.transition b t ∧ s a₁ y₁,
      from h₅_left t a₁ h₆,
      cases h₇,
      rename h₇_w b₁,
      fconstructor,
      exact b₁,
      split,
      tauto,
      have h₈ : P.bisimilar a₁ b₁,
      fconstructor,
      exact s,
      tauto,
      exact (relation.conj_relation 
        (relation.relation2 x y)).mem_union_right h₈,
    },
    {
      intro t,
      intro b₁,
      assume s₂,
      cases s₂,
      have c₁ : b = y ∨ b ≠ y,
      tauto,
      cases c₁,
      have c₂ : a = y ∨ a = x ∨ (a≠x ∧ a≠y),
      tauto,
      cases c₂,
      fconstructor,
      exact b₁,
      split,
      have h : a = b,
      subst c₂,
      tauto,
      subst h,
      from s₂_right,
      have h : P.strong_bisimilarity b₁ b₁,
      fconstructor,
      exact relation.identity_relation,
      split,
      tauto,
      from lts.bisimulation.identity_relation P,
      suffices h₁ : (b₁,b₁) ∈ con_r,
      tauto,
      suffices h₂ : (b₁,b₁) ∈ (relation.conj_relation 
        P.strong_bisimilarity),
      exact (relation.conj_relation (relation.relation2 x 
        y)).mem_union_right h,
      fconstructor,
      exact relation.identity_relation,
      split,
      tauto,
      from lts.bisimulation.identity_relation P,
      cases c₂,
      have h : ∃ (a₁ : proc), a₁ ∈ P.transition x t ∧ P.strong_bisimilarity 
        a₁ b₁,
      have h₁ : b₁ ∈ P.transition y t,
      subst c₁,
      from s₂_right,
      from s₁_right t b₁ h₁,
      cases h,
      fconstructor,
      exact h_w,
      cases h_h,
      split,
      subst c₂,
      from h_h_left,
      exact (relation.conj_relation 
        (relation.relation2 x y)).mem_union_right h_h_right,
      cases c₂,
      suffices h : (a,b) ∈ (relation.conj_relation P.strong_bisimilarity),
      have h₁ : P.strong_bisimilarity a b,
      tauto,
      have h₂ : ∃ (s : proc → proc → Prop), (s a b) ∧ P.bisimulation s,
      from h₁,
      cases h₂,
      rename h₂_w s,
      cases h₂_h,
      have h₃ : (∀ t (y₁ : proc), (s a b ∧ y₁ ∈ P.transition 
        a t) → ∃ (b₁ : proc), (b₁ ∈ P.transition b t ∧ (s y₁ b₁))) ∧ 
        (∀ t (b₁ : proc), (s a b ∧ b₁ ∈ P.transition b t) → ∃ (y₁ : proc), 
        (y₁ ∈ P.transition a t ∧ (s y₁ b₁))),
      from h₂_h_right a b,
      cases h₃,
      have h₄ : s a b ∧ b₁ ∈ P.transition b t,
      split,
      from h₂_h_left,
      from s₂_right,
      have h₅ : ∃ (y₁ : proc), y₁ ∈ P.transition a t ∧ s y₁ b₁,
      from h₃_right t b₁ h₄,
      cases h₅,
      rename h₅_w a₁,
      fconstructor,
      exact a₁,
      split,
      tauto,
      have h₆ : P.bisimilar a₁ b₁,
      fconstructor,
      exact s,
      tauto,
      exact (relation.conj_relation 
        (relation.relation2 x y)).mem_union_right h₆,
      have h₁ : P.strong_bisimilarity a b,
      have h₂ : r a b → (a = x ∧ b = y) ∨ P.strong_bisimilarity a b,
      exact (set.mem_union (a, b) 
        (relation.conj_relation (relation.relation2 x y)) 
        (relation.conj_relation (LTS.strong_bisimilarity P))).mp,
      have h₃ : (a = x ∧ b = y) ∨ P.strong_bisimilarity a b,
      from h₂ s₂_left,
      tauto,
      from h₁,
      have h₁ : r a b → (a = x ∧ b = y) ∨ P.strong_bisimilarity a b,
      exact (set.mem_union (a, b) 
        (relation.conj_relation (relation.relation2 x y)) 
        (relation.conj_relation (LTS.strong_bisimilarity P))).mp,
      have h₂ : (a = x ∧ b = y) ∨ P.strong_bisimilarity a b,
      from h₁ s₂_left,
      have h₃ : P.strong_bisimilarity a b,
      tauto,
      have h₄ : ∃ (s : proc → proc → Prop), (s a b) ∧ P.bisimulation s,
      from h₃,
      cases h₄,
      rename h₄_w s,
      cases h₄_h,
      have h₅ : (∀ t (y₁ : proc), (s a b ∧ y₁ ∈ P.transition a t) → ∃ (b₁ : 
        proc), (b₁ ∈ P.transition b t ∧ (s y₁ b₁))) ∧ (∀ t (b₁ : proc), 
        (s a b ∧ b₁ ∈ P.transition b t) → ∃ (y₁ : proc), (y₁ ∈ P.transition 
        a t ∧ (s y₁ b₁))),
      from h₄_h_right a b,
      cases h₅,
      have h₆ : s a b ∧ b₁ ∈ P.transition b t,
      split,
      from h₄_h_left,
      from s₂_right,
      have h₇ : ∃ (y₁ : proc), y₁ ∈ P.transition a t ∧ s y₁ b₁,
      from h₅_right t b₁ h₆,
      cases h₇,
      rename h₇_w a₁,
      fconstructor,
      exact a₁,
      split,
      tauto,
      have h₈ : P.bisimilar a₁ b₁,
      fconstructor,
      exact s,
      tauto,
      exact (relation.conj_relation 
        (relation.relation2 x y)).mem_union_right h₈,
    },
  },
end







-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
--                                      CCS
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------


inductive ccs (lab : Type u) (nam : Type v)
|zer : ccs
|ap (a:lab) (u:ccs) : ccs
|pq (p:ccs) (q:ccs) : ccs
|psq (p:ccs) (q:ccs) : ccs
|name (n:nam) (p:ccs) : ccs
|named (n:nam): ccs

export ccs (zer ap pq psq name named)


namespace ccs

variables {lab : Type u} {nam : Type v} 
  [decidable_eq lab] [decidable_eq nam]


def sust: ccs lab nam → nam → ccs lab nam → ccs lab nam
|r n zer:= zer
|r n (ap a p) := (ap a (sust r n p))
|r n (pq p q) := (pq (sust r n p) (sust r n q))
|r n (psq p q) := (psq (sust r n p) (sust r n q))
|r n (name m p) := (name m (sust r n p))
|r n (named m) := if n = m then r else (named m)

def simp: ccs lab nam → ccs lab nam
|(name m p) := sust (name m p) m p
|q := q

def utransition : ccs lab nam → lab → ccs lab nam →Prop
|(ap a p) b r := a = b ∧ p = r
|(pq p q) a r := (∃ c, utransition p a c ∧ r = (pq c q)) ∨ 
  (∃ c, utransition q a c ∧ r = (pq p c))
|(psq p q) a r := (utransition p a r) ∨ (utransition q a r)
|_ _ _ := ff

def rest_utransition : ccs lab nam → ccs lab nam → Prop
|(pq p q) r := (∃ c, rest_utransition p c ∧ r = (pq c q)) ∨ 
  (∃ c, rest_utransition q c ∧ r = (pq p c))
|(psq p q) r := (rest_utransition p r) ∨ (rest_utransition q r)
|(name m p) r := r = simp (name m p)
|_ _ := ff

def transition_n : ccs lab nam → lab → ccs lab nam → ℕ → Prop
|u a r 0 := utransition u a r
|u a r (k + 1) := (transition_n u a r k) ∨  
  (∃ c, (rest_utransition u c) ∧ (transition_n c a r k))

def transition (p : ccs lab nam) (a : lab) (q : ccs lab nam): Prop := 
  ∃ n, (transition_n p a q n)

-- Relacion auxiliar de recursion de rest_utransition y 
-- equivalencia definicional

def rest_utransition_n : ccs lab nam → ccs lab nam → ℕ → Prop
|p q 0 := rest_utransition p q
|p q (k + 1) := ∃ c, rest_utransition p c ∧ rest_utransition_n c q k

def definitional_equivalence : ccs lab nam → ccs lab nam → Prop
|p q := ∃ n, rest_utransition_n p q n

-- Bisimulacion Fuerte

def bisimulation (r : ccs lab nam → ccs lab nam → Prop) := 
  ∀ p q, (∀ (a : lab) (p₁ : ccs lab nam), (r p q ∧ transition p a p₁) → 
  ∃ (q₁ : ccs lab nam), (transition q a q₁ ∧ (r p₁ q₁))) ∧ (∀ (b : lab) 
  (q₁ : ccs lab nam), (r p q ∧ transition q b q₁) → ∃ (p₁ : ccs lab nam), 
  (transition p b p₁ ∧ (r p₁ q₁)))

def bisimilar (p q : ccs lab nam) := 
  ∃ (s:ccs lab nam → ccs lab nam → Prop), (s p q) ∧ bisimulation s

def strong_bisimilarity: ccs lab nam → ccs lab nam → Prop
|p q := bisimilar p q


-- Vamos a asignar los simbolos usuales de ccs a nuestras definiciones
-- Para ello primero creamos unas funciones

def add : ccs lab nam → ccs lab nam → ccs lab  nam
|p q := psq p q

def par : ccs lab nam → ccs lab nam → ccs lab nam
|p q := pq p q

def lab_tran : lab → ccs lab nam → ccs lab nam
|a p := ap a p

-- Asignamos ahora a cada simbolo su funcion

infix ` + `:50 := ccs.add

infix ` ∣ `:50 := ccs.par

infix ` . `:55 := ccs.lab_tran

infix ` ∼ `:40 := ccs.strong_bisimilarity

-- Comprobamos que las asignaciones de simbolos funcionen correctamente

#check ("input" . zer : ccs string string)
#check (zer ∣ zer : ccs lab nam)
#check ("output" . (zer + zer): ccs string string) 
#check (zer) ∼ (zer + zer)
#check ("input" . zer ∣ zer : ccs string string) ∼ zer
#check zer 

-- La definicion de buffer1 intenta imitar B₀¹ del libro:
-- Reactive Systems: Modelling, Specification and Verification

def buffer1_0 : ccs string string:= name "x" ("in" . ("out" . (named "x")))
def buffer1_1 : ccs string string:= name "x" ("out" . ("in" . (named "x")))

-- La definicion de buffer2 intenta imitar (B₀¹ | B₀¹)

def buffer2 : ccs string string:= buffer1_1 ∣ buffer1_0

-- La definicion de buffer2_2 intenta imitar b₀² 

def buffer2_2_1 : ccs string string:= name "x₁" ("in" . ("out" . 
  (named "x₁")) + "out" . ( "in" . (named "x₁")))


-- Funciones auxiliares para  demostraciones

def funcion1 : ccs lab nam → ccs lab nam → ccs lab nam → Prop 
|p q r := r = (p + q)

def funcion2 : ccs lab nam → ccs lab nam → ccs lab nam → Prop 
|p q r := r = (q + p)

end ccs


-- Probamos ciertos resultados sencillos

variables {lab X: Type u} {nam : Type v} 
  [decidable_eq lab] [decidable_eq nam]


lemma ccs.bisimulation.identity_relation : ccs.bisimulation 
  (relation.identity_relation : ccs lab nam → ccs lab nam → Prop) := 
begin
  intro,
  intro,
  split,
  {
    intro,
    intro z,
    assume a₁,
    cases a₁,
    have h₁ : relation.identity_relation p q → q = p,
    tauto,
    have h₂ : q = p,
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
    have h₁ : relation.identity_relation p q → q = p,
    tauto,
    have h₂ : q = p,
    tauto,
    fconstructor,
    exact z,
    split,
    finish,
    tauto,
  },
end

lemma ccs.bisimilar.symmetric: 
  symmetric (ccs.bisimilar : ccs lab nam → ccs lab nam → Prop) :=
begin
  intro,
  intro,
  assume a,
  have h₁ : ∃ (r:ccs lab nam → ccs lab nam → Prop), (r x y) ∧ 
    ccs.bisimulation r,
  from a,
  cases h₁,
  rename h₁_w r,
  let r₁ := relation.inverted_binary_relation r,
  fconstructor,
  exact r₁,
  cases h₁_h,
  have h₂ : ∀ x y, (∀ (a : lab) (x₁ : ccs lab nam), (r x y ∧ 
    ccs.transition x a x₁) → ∃ (y₁ : ccs lab nam), (ccs.transition y a y₁ 
    ∧ (r x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab nam), (r x y ∧ ccs.transition 
    y b y₁) → ∃ (x₁ : ccs lab nam), (ccs.transition x b x₁ ∧ (r x₁ y₁))),
  from h₁_h_right,
  split,
  from h₁_h_left,
  suffices s₁ : ∀ x y, (∀ (a : lab) (x₁ : ccs lab nam), (r₁ x y ∧ 
    ccs.transition x a x₁) → ∃ (y₁ : ccs lab nam), (ccs.transition y a y₁ 
    ∧ (r₁ x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab nam), (r₁ x y ∧ 
    ccs.transition y b y₁) → ∃ (x₁ : ccs lab nam), (ccs.transition x b x₁ 
    ∧ (r₁ x₁ y₁))),
  tauto,
  intro z,
  intro w,
  have h₃ : (∀ (a : lab) (x₁ : ccs lab nam), (r w z ∧ ccs.transition 
    w a x₁) → ∃ (y₁ : ccs lab nam), (ccs.transition z a y₁ ∧ (r x₁ y₁))) 
    ∧ (∀ (b : lab) (y₁ : ccs lab nam), (r w z ∧ ccs.transition z b y₁) → 
    ∃ (x₁ : ccs lab nam), (ccs.transition w b x₁ ∧ (r x₁ y₁))),
  from h₂ w z,
  cases h₃,
  split,
  {
    intro l,
    intro z₁,
    assume a₁,
    have h₄ : r w z ∧ z.transition l z₁,
    from a₁,
    have h₅ : (r w z ∧ z.transition l z₁) → (∃ (w₁ : ccs lab nam), 
      w.transition l w₁ ∧ r w₁ z₁),
    from h₃_right l z₁,
    from h₅ h₄,
  },
  {
    intro l,
    intro w₁,
    assume a₁,
    have h₄ : r w z ∧ w.transition l w₁,
    from a₁,
    have h₅ : (r w z ∧ w.transition l w₁) → (∃ (z₁ : ccs lab nam), 
      z.transition l z₁ ∧ r w₁ z₁),
    from h₃_left l w₁,
    from h₅ h₄,
  },
end

lemma ccs.bisimilar.reflexive: 
  reflexive (ccs.bisimilar : ccs lab nam → ccs lab nam → Prop) :=
begin
  intro,
  let r : (ccs lab nam → ccs lab nam → Prop) := 
    relation.identity_relation,
  fconstructor,
  exact r,
  split,
  fconstructor,
  exact ccs.bisimulation.identity_relation,
end

lemma ccs.bisimilar_left: ∀ (r : ccs lab nam → ccs lab nam → Prop), 
  ccs.bisimulation r → ∀ p q, (∀ (a : lab) (p₁ : ccs lab nam), 
  (r p q ∧ ccs.transition p a p₁) → ∃ (q₁ : ccs lab nam), (ccs.transition 
  q a q₁ ∧ (r p₁ q₁))) :=
begin
  intro,
  assume a₁,
  intro,
  intro,
  have h₁ : (∀ (a : lab) (x₁ : ccs lab nam), (r p q ∧ ccs.transition 
    p a x₁) → ∃ (y₁ : ccs lab nam), (ccs.transition q a y₁ ∧ (r x₁ y₁))) 
    ∧ (∀ (b : lab) (y₁ : ccs lab nam), (r p q ∧ ccs.transition q b y₁) → 
    ∃ (x₁ : ccs lab nam), (ccs.transition p b x₁ ∧ (r x₁ y₁))),
  from a₁ p q,
  cases h₁,
  exact h₁_left,
end

lemma ccs.bisimilar_right: ∀ (r : ccs lab nam → ccs lab nam → Prop), 
  ccs.bisimulation r → ∀ p q, (∀ (a : lab) (q₁ : ccs lab nam), (r p q 
  ∧ ccs.transition q a q₁) → ∃ (p₁ : ccs lab nam), (ccs.transition 
  p a p₁ ∧ (r p₁ q₁))) :=
begin
  intro,
  assume a₁,
  intro,
  intro,
  have h₁ : (∀ (a : lab) (x₁ : ccs lab nam), (r p q ∧ ccs.transition 
    p a x₁) → ∃ (y₁ : ccs lab nam), (ccs.transition q a y₁ ∧ (r x₁ y₁))) 
    ∧ (∀ (b : lab) (y₁ : ccs lab nam), (r p q ∧ ccs.transition q b y₁) → 
    ∃ (x₁ : ccs lab nam), (ccs.transition p b x₁ ∧ (r x₁ y₁))),
  from a₁ p q,
  cases h₁,
  exact h₁_right,
end

lemma ccs.bisimilar.transitive: 
  transitive (ccs.bisimilar : ccs lab nam → ccs lab nam → Prop) :=
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
      have h₁ : ∃ (e : ccs lab nam), r₁ q e ∧ r₂ e w,
      tauto,
      cases h₁,
      rename h₁_w e,
      have h₂ : ∀ x y, (∀ (a : lab) (x₁ : ccs lab nam), (r₁ x y ∧ 
        ccs.transition x a x₁) → ∃ (y₁ : ccs lab nam), (ccs.transition 
        y a y₁ ∧ (r₁ x₁ y₁))),
      exact ccs.bisimilar_left r₁ a₁_h_right,
      have h₃ : ∃ (e₁ : ccs lab nam), e.transition t e₁ ∧ r₁ q₁ e₁,
      have h₄ : r₁ q e ∧ ccs.transition q t q₁,
      tauto,
      from h₂ q e t q₁ h₄,
      cases h₃,
      rename h₃_w e₁,
      have h₅ : ∀ x y, (∀ (a : lab) (x₁ : ccs lab nam), (r₂ x y ∧ 
        ccs.transition x a x₁) → ∃ (y₁ : ccs lab nam), (ccs.transition 
        y a y₁ ∧ (r₂ x₁ y₁))),
      exact ccs.bisimilar_left r₂ a₂_h_right,
      have h₆ : ∃ (w₁ : ccs lab nam), w.transition t w₁ ∧ r₂ e₁ w₁,
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
      have h₁ : ∃ (e : ccs lab nam), r₁ q e ∧ r₂ e w,
      tauto,
      cases h₁,
      rename h₁_w e,
      have h₂ : ∀ x y, (∀ (a : lab) (y₁ : ccs lab nam), (r₂ x y ∧ 
        ccs.transition y a y₁) → ∃ (x₁ : ccs lab nam), (ccs.transition 
        x a x₁ ∧ (r₂ x₁ y₁))),
      exact ccs.bisimilar_right r₂ a₂_h_right,
      have h₃ : ∃ (e₁ : ccs lab nam), e.transition t e₁ ∧ r₂ e₁ w₁,
      have h₄ : r₂ e w ∧ ccs.transition w t w₁,
      tauto,
      from h₂ e w t w₁ h₄,
      cases h₃,
      rename h₃_w e₁,
      have h₅ : ∀ x y, (∀ (a : lab) (y₁ : ccs lab nam), (r₁ x y ∧ 
        ccs.transition y a y₁) → ∃ (x₁ : ccs lab nam), (ccs.transition 
        x a x₁ ∧ (r₁ x₁ y₁))),
      exact ccs.bisimilar_right r₁ a₁_h_right,
      have h₆ : ∃ (q₁ : ccs lab nam), q.transition t q₁ ∧ r₁ q₁ e₁,
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
  (ccs.strong_bisimilarity : ccs lab nam → ccs lab nam → Prop) :=
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
      have h₂ : symmetric ccs.bisimilar → (ccs.bisimilar x y → 
        ccs.bisimilar y x),
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
      have h₃ : transitive ccs.bisimilar → (ccs.bisimilar x y ∧ 
        ccs.bisimilar y z → ccs.bisimilar x z),
      tauto,
      have h₄ : ccs.bisimilar x y ∧ ccs.bisimilar y z,
      tauto,
      exact h₃ ccs.bisimilar.transitive h₄,
    },
  },
end

theorem ccs.strong_bisimilarity.is_bisimulation : ccs.bisimulation 
  (ccs.strong_bisimilarity : ccs lab nam → ccs lab nam → Prop) :=
begin
  let r := (ccs.strong_bisimilarity : ccs lab nam → ccs lab nam → Prop),
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
    have h₁ : ccs.bisimilar p q,
    tauto,
    have h₂ : ∃ (s:ccs lab nam → ccs lab nam → Prop), (s p q) ∧ ccs.bisimulation s,
    tauto,
    cases h₂,
    rename h₂_w s,
    suffices s₂ : ∃ (q₁ : ccs lab nam), q.transition l q₁ ∧ s p₁ q₁,
    {
      cases s₂,
      rename s₂_w q₁,
      fconstructor,
      exact q₁,
      split,
      tauto,
      fconstructor,
      exact s,
      tauto,
    },
    {
      have h₃ : (∀ (a : lab) (x₁ : ccs lab nam), (s p q ∧ p.transition 
        a x₁) → ∃ (y₁ : ccs lab nam), (q.transition a y₁ ∧ (s x₁ y₁))) 
        ∧ (∀ (b : lab) (y₁ : ccs lab nam), (s p q ∧ q.transition b y₁) 
        → ∃ (x₁ : ccs lab nam), (p.transition b x₁ ∧ (s x₁ y₁))),
      cases h₂_h,
      from h₂_h_right p q,
      cases h₃,
      have h₄ : s p q ∧ p.transition l p₁,
      tauto,
      from h₃_left l p₁ h₄,
    },
  },
  {
    intro l,
    intro,
    assume a₁,
    cases a₁,
    have h₁ : ccs.bisimilar p q,
    tauto,
    have h₂ : ∃ (s : ccs lab nam → ccs lab nam → Prop), (s p q) ∧ 
      ccs.bisimulation s,
    tauto,
    cases h₂,
    rename h₂_w s,
    suffices s₂ : ∃ (x₁ : ccs lab nam), p.transition l x₁ ∧ s x₁ q₁,
    {
      cases s₂,
      rename s₂_w p₁,
      fconstructor,
      exact p₁,
      split,
      tauto,
      fconstructor,
      exact s,
      tauto,
    },
    {
      have h₃ : (∀ (a : lab) (x₁ : ccs lab nam), (s p q ∧ p.transition 
        a x₁) → ∃ (y₁ : ccs lab nam), (q.transition a y₁ ∧ (s x₁ y₁))) 
        ∧ (∀ (b : lab) (y₁ : ccs lab nam), (s p q ∧ q.transition b y₁) 
        → ∃ (x₁ : ccs lab nam), (p.transition b x₁ ∧ (s x₁ y₁))),
      cases h₂_h,
      from h₂_h_right p q,
      cases h₃,
      have h₄ : s p q ∧ q.transition l q₁,
      tauto,
      from h₃_right l q₁ h₄, 
    }
  },
end

lemma ccs.strong_bisimilarity.supset.bisimulation : ∀ (r:ccs lab nam → 
  ccs lab nam → Prop), ccs.bisimulation r → (∀ p q, r p q → 
  ccs.strong_bisimilarity p q) :=
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

theorem ccs.strong_bisimilarity.is_largest_bisimulation : ∀ (s:ccs lab nam 
  → ccs lab nam → Prop), ccs.bisimulation s → (cardinal.mk 
  (relation.conj_relation (ccs.strong_bisimilarity : ccs lab nam → 
  ccs lab nam → Prop))) >= (cardinal.mk (relation.conj_relation s)) :=
begin
  intro s,
  let r := (ccs.strong_bisimilarity : ccs lab nam → ccs lab nam → Prop),
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

theorem ccs.strong_bisimilarity.nat_rec_decomp_bisimilarity : ∀ (p q : ccs 
  lab nam), ( ( ∀ (t : lab) (p₁ : ccs lab nam), p.transition t p₁ → ∃ 
  (q₁ : ccs lab nam), q.transition t q₁ ∧ ccs.strong_bisimilarity p₁ q₁ ) 
  ∧ ( ∀ (t : lab) (q₁ : ccs lab nam), q.transition t q₁ → ∃ (p₁ : ccs lab 
  nam), p.transition t p₁ ∧ ccs.strong_bisimilarity p₁ q₁ ) ) → 
  ccs.strong_bisimilarity p q :=
begin
  intro x,
  intro y,
  assume a₁,
  cases a₁,
  let r := relation.join_relations (relation.relation2 x y) 
    ccs.strong_bisimilarity,
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
          (ccs.strong_bisimilarity : ccs lab nam → ccs lab nam → Prop)), 
        exact (relation.conj_relation 
          (relation.relation2 x y)).mem_union_right h₁,
        fconstructor,
        exact relation.identity_relation,
        split,
        tauto,
        from ccs.bisimulation.identity_relation,
      },
      {
        cases ca₂,
        {
          have h₂ : ∃ (d₁ : ccs lab nam) , y.transition l d₁ ∧ 
            ccs.strong_bisimilarity c₁ d₁,
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
          exact (relation.conj_relation 
            (relation.relation2 x y)).mem_union_right h₂_h_right,
        },
        {
          cases ca₂,
          suffices h₄ : (c,d) ∈ (relation.conj_relation 
            (ccs.strong_bisimilarity : ccs lab nam → ccs lab nam → Prop)),
          {
            have h₅ : ccs.strong_bisimilarity c d,
            tauto,
            have h₆ : ∃ (s : ccs lab nam → ccs lab nam → Prop), (s c d) ∧ 
              ccs.bisimulation s,
            from h₅,
            cases h₆,
            rename h₆_w s,
            cases h₆_h,
            have h₇ : (∀ t (c₁ : ccs lab nam), (s c d ∧ c.transition t c₁) 
              → ∃ (d₁ : ccs lab nam), (d.transition t d₁ ∧ (s c₁ d₁))) ∧ 
              (∀ t (d₁ : ccs lab nam), (s c d ∧ d.transition t d₁) → ∃ 
              (c₁ : ccs lab nam), (c.transition t c₁ ∧ (s c₁ d₁))),
            from h₆_h_right c d,
            cases h₇,
            have h₈ : s c d ∧ c.transition l c₁,
            split,
            from h₆_h_left,
            from a₂_right,
            have h₉ : ∃ (d₁ : ccs lab nam), d.transition l d₁ ∧ s c₁ d₁,
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
            exact (relation.conj_relation 
              (relation.relation2 x y)).mem_union_right h₁₀,
          },
          {
            have h₁ : ccs.strong_bisimilarity c d,
            have h₂ : r c d → (c = x ∧ d = y) ∨ ccs.strong_bisimilarity 
              c d,
            exact (set.mem_union (c, d) 
              (relation.conj_relation (relation.relation2 x y))
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
        exact (set.mem_union (c, d) 
          (relation.conj_relation (relation.relation2 x y))
          (relation.conj_relation (ccs.strong_bisimilarity))).mp,
        have h₂ : (c = x ∧ d = y) ∨ ccs.strong_bisimilarity c d,
        from h₁ a₂_left,
        have h₃ : ccs.strong_bisimilarity c d,
        tauto,
        have h₄ : ∃ (s : ccs lab nam → ccs lab nam → Prop), (s c d) ∧ 
          ccs.bisimulation s,
        from h₃,
        cases h₄,
        rename h₄_w s,
        cases h₄_h,
        have h₅ : (∀ a (x₁ : ccs lab nam), (s c d ∧ c.transition a x₁) → 
          ∃ (y₁ : ccs lab nam), (d.transition a y₁ ∧ (s x₁ y₁))) ∧ 
          (∀ b (y₁ : ccs lab nam), (s c d ∧ d.transition b y₁) → ∃ 
          (x₁ : ccs lab nam), (c.transition b x₁ ∧ (s x₁ y₁))),
        from h₄_h_right c d,
        cases h₅,
        have h₆ : s c d ∧ c.transition l c₁,
        split,
        from h₄_h_left,
        from a₂_right,
        have h₇ : ∃ (y₁ : ccs lab nam), d.transition l y₁ ∧ s c₁ y₁,
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
        exact (relation.conj_relation 
          (relation.relation2 x y)).mem_union_right h₈,
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
          (ccs.strong_bisimilarity : ccs lab nam → ccs lab nam → Prop)),
        exact (relation.conj_relation 
          (relation.relation2 x y)).mem_union_right h₁,
        fconstructor,
        exact relation.identity_relation,
        split,
        tauto,
        from ccs.bisimulation.identity_relation,
      },
      {
        cases ca₂,
        {
          have h₁ : ∃(c₁ : ccs lab nam), x.transition l c₁ ∧ 
            ccs.strong_bisimilarity c₁ d₁,
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
          exact (relation.conj_relation 
            (relation.relation2 x y)).mem_union_right h₁_h_right,
        },
        {
          cases ca₂,
          suffices h₁ : (c,d)∈ (relation.conj_relation 
            (ccs.strong_bisimilarity : ccs lab nam → ccs lab nam → Prop)),
          {
            have h₂ : ccs.strong_bisimilarity c d,
            tauto,
            have h₃ : ∃ (s : ccs lab nam → ccs lab nam → Prop), (s c d) ∧ 
              ccs.bisimulation s,
            from h₂,
            cases h₃,
            rename h₃_w s,
            cases h₃_h,
            have h₄ : (∀ t (x₁ : ccs lab nam), (s c d ∧ c.transition 
              t x₁) → ∃ (c₁ : ccs lab nam), (d.transition t c₁ ∧ (s x₁ 
              c₁))) ∧ (∀ t (d₁ : ccs lab nam), (s c d ∧ d.transition t 
              d₁) → ∃ (c₁ : ccs lab nam), (c.transition t c₁ ∧ (s c₁ d₁))),
            from h₃_h_right c d,
            cases h₄,
            have h₅ : s c d ∧ d.transition l d₁,
            split,
            from h₃_h_left,
            from a₂_right,
            have h₆ : ∃ (y₁ : ccs lab nam), c.transition l y₁ ∧ s y₁ d₁,
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
            exact (relation.conj_relation 
              (relation.relation2 x y)).mem_union_right h₇,
          },
          {
            have h₁ : ccs.strong_bisimilarity c d,
            have h₂ : r c d → (c = x ∧ d = y) ∨ ccs.strong_bisimilarity 
              c d,
            exact (set.mem_union (c, d) 
              (relation.conj_relation (relation.relation2 x y))
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
        exact (set.mem_union (c, d) 
          (relation.conj_relation (relation.relation2 x y))
          (relation.conj_relation (ccs.strong_bisimilarity))).mp,
        have h₂ : (c = x ∧ d = y) ∨ ccs.strong_bisimilarity c d,
        from h₁ a₂_left,
        have h₃ : ccs.strong_bisimilarity c d,
        tauto,
        have h₄ : ∃ (s : ccs lab nam → ccs lab nam → Prop), (s c d) ∧ 
          ccs.bisimulation s,
        from h₃,
        cases h₄,
        rename h₄_w s,
        cases h₄_h,
        have h₅ : (∀ t (y₁ : ccs lab nam), (s c d ∧ c.transition t y₁) → 
          ∃ (d₁ : ccs lab nam), (d.transition t d₁ ∧ (s y₁ d₁))) ∧ (∀ t 
          (d₁ : ccs lab nam), (s c d ∧ d.transition t d₁) → ∃ (y₁ : ccs 
          lab nam), (c.transition t y₁ ∧ (s y₁ d₁))),
        from h₄_h_right c d,
        cases h₅,
        have h₆ : s c d ∧ d.transition l d₁,
        split,
        from h₄_h_left,
        from a₂_right,
        have h₇ : ∃ (y₁ : ccs lab nam), c.transition l y₁ ∧ s y₁ d₁,
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
        exact (relation.conj_relation 
          (relation.relation2 x y)).mem_union_right h₈,
      },
    },
  },
end

lemma relation.join_relations_right : ∀ (r s : X → X → Prop) (x y : X), 
  s x y → (relation.join_relations r s) x y :=
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

lemma ccs.transition_ap : ∀ (p : ccs lab nam) (t : lab), ccs.transition 
  (t . p) t p :=
begin
  intro x,
  intro,
  fconstructor,
  exact 0,
  fconstructor,
  tauto,
  tauto,
end

lemma ccs.transtion_ap_only : ∀ (p q : ccs lab nam) (t : lab), 
  ccs.transition (t . p) t q → q = p :=
begin
  intro x,
  intro y,
  intro,
  assume a₁,
  cases a₁,
  rename a₁_w n,
  induction n,
  {
    cases a₁_h,
    tauto,
  },
  {
    cases a₁_h,
    {
      exact n_ih a₁_h,
    },
    {
      cases a₁_h,
      cases a₁_h_h,
      cases a₁_h_h_left,
    },
  },
end

lemma ccs.transition_ap_a : ∀ (p q: ccs lab nam) (t l : lab), 
  ccs.transition (t . p) l q → l = t :=
begin
  intro x,
  intro y,
  intro,
  intro,
  assume a₁,
  cases a₁,
  rename a₁_w n,
  induction n,
  {
    cases a₁_h,
    tauto,
  },
  {
    cases a₁_h,
    {
      exact n_ih a₁_h,
    },
    {
      cases a₁_h,
      cases a₁_h_h,
      cases a₁_h_h_left,
    },
  },
end

theorem ccs.property_ap_bisimilar : ∀ (p q : ccs lab nam) (t : lab), 
  p ∼ q → (t . p) ∼ (t . q) := 
begin
  intro x,
  intro y,
  intro,
  assume a₁,
  cases a₁,
  cases a₁_h,
  rename a₁_w r,
  let s := relation.join_relations (relation.relation2 (t . x) (t . y)) r,
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
      have c₁ : p = (t . x) ∨ p ≠ (t . x),
      tauto,
      cases c₁,
      {
        have c₂ : q = (t . y) ∨ q ≠ (t . y),
        tauto,
        cases c₂,
        {
          have h₁ : (t . x).transition l p₁,
          subst c₁,
          exact a₂_right,
          have h₂ : l = t,
          exact ccs.transition_ap_a x p₁ t l h₁,
          have h₃ : (t . x).transition t p₁ → p₁ = x,
          exact ccs.transtion_ap_only x p₁ t,
          have h₄ : p₁ = x,
          subst h₂,
          exact h₃ h₁,
          fconstructor,
          exact y,
          split,
          suffices s₁ : ccs.transition (t . y) t y,
          subst h₂,
          subst c₂,
          exact s₁,
          exact ccs.transition_ap y t,
          suffices s₁ : s x y,
          subst h₄,
          exact s₁,
          exact relation.join_relations_right (relation.relation2 (t . x) 
            (t . y)) r x y a₁_h_left,
        },
        {
          have h₁ : s p q → (p = (t . x) ∧ q = (t . y)) ∨ r p q,
          exact (set.mem_union (p, q) (relation.conj_relation 
            (relation.relation2 (t . x) (t . y))) (relation.conj_relation 
            r)).mp,
          have h₂ : (p = (t . x) ∧ q = (t . y)) ∨ r p q,
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
          exact relation.join_relations_right (relation.relation2 (t . x) 
            (t . y)) r p₁ q₁ h₅_h_right,
        },
      },
      {
        have h₁ : s p q → (p = (t . x) ∧ q = (t . y)) ∨ r p q,
        exact (set.mem_union (p, q) (relation.conj_relation 
          (relation.relation2 (t . x) (t . y))) (relation.conj_relation 
          r)).mp,
        have h₂ : (p = (t . x) ∧ q = (t . y)) ∨ r p q,
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
        exact relation.join_relations_right (relation.relation2 (t . x) 
          (t . y)) r p₁ q₁ h₅_h_right,
      },
    },
    {
      intro l,
      intro q₁,
      assume a₂,
      cases a₂,
      have c₁ : p = (t . x) ∨ p ≠ (t . x),
      tauto,
      cases c₁,
      {
        have c₂ : q = (t . y) ∨ q ≠ (t . y),
        tauto,
        cases c₂,
        {
          have h₁ : (t . y).transition l q₁,
          subst c₂,
          exact a₂_right,
          have h₂ : l = t,
          exact ccs.transition_ap_a y q₁ t l h₁,
          have h₃ : (t . y).transition t q₁ → q₁ = y,
          exact ccs.transtion_ap_only y q₁ t,
          have h₄ : q₁ = y,
          subst h₂,
          exact h₃ h₁,
          fconstructor,
          exact x,
          split,
          suffices s₁ : ccs.transition (t . x) t x,
          subst h₂,
          subst c₁,
          exact s₁,
          exact ccs.transition_ap x t,
          suffices s₁ : s x y,
          subst h₄,
          exact s₁,
          exact relation.join_relations_right (relation.relation2 (t . x) 
            (t . y)) r x y a₁_h_left,
        },
        {
          have h₁ : s p q → (p = (t . x) ∧ q = (t . y)) ∨ r p q,
          exact (set.mem_union (p, q) (relation.conj_relation 
            (relation.relation2 (t . x) (t . y))) (relation.conj_relation 
            r)).mp,
          have h₂ : (p = (t . x) ∧ q = (t . y)) ∨ r p q,
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
          exact relation.join_relations_right (relation.relation2 (t . x) 
            (t . y)) r p₁ q₁ h₅_h_right,
        },
      },
      {
        have h₁ : s p q → (p = (t . x) ∧ q = (t . y)) ∨ r p q,
        exact (set.mem_union (p, q) (relation.conj_relation 
          (relation.relation2 (t . x) (t . y))) (relation.conj_relation 
          r)).mp,
        have h₂ : (p = (t . x) ∧ q = (t . y)) ∨ r p q,
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
        exact relation.join_relations_right (relation.relation2 (t . x) 
          (t . y)) r p₁ q₁ h₅_h_right,
      },
    },
  },
end

lemma ccs.transition_psq_1 : ∀ (p q w p₁: ccs lab nam) (t : lab), 
  ccs.funcion1 q w p ∧ ccs.transition p t p₁ → ccs.transition q t p₁ 
  ∨ ccs.transition w t p₁ :=
begin
  intro x,
  intro a,
  intro b,
  intro x₁,
  intro t,
  assume a₁,
  cases a₁,
  have h₁ : ccs.funcion1 a b x → x = (a + b : ccs lab nam),
  tauto,
  have h₂ : x = (a + b : ccs lab nam),
  tauto,
  suffices s₁ : ccs.transition (a + b) t x₁ → ccs.transition a t x₁ ∨ 
    ccs.transition b t x₁,
  subst h₂,
  exact s₁ a₁_right,
  assume a₂,
  cases a₂,
  rename a₂_w n,
  induction n,
  {
    cases a₂_h,
    {
      suffices s : a.transition t x₁,
      tauto,
      fconstructor,
      exact 0,
      tauto,
    },
    {
      suffices s : b.transition t x₁,
      tauto,
      fconstructor,
      exact 0,
      tauto,
    },
  },
  {
    cases a₂_h,
    {
      exact n_ih a₂_h,
    },
    {
      cases a₂_h,
      cases a₂_h_h,
      cases a₂_h_h_left,
      {
        suffices s : a.transition t x₁,
        tauto,
        fconstructor,
        exact (n_n.add 1 : ℕ),
        suffices s : (a.transition_n t x₁ n_n) ∨ 
          (∃ c, (a.rest_utransition c) ∧ (c.transition_n t x₁ n_n)),
        tauto,
        suffices s : (∃ c, (a.rest_utransition c) ∧ 
          (c.transition_n t x₁ n_n)),
        tauto,
        fconstructor,
        exact a₂_h_w,
        tauto,
      },
      {
        suffices s : b.transition t x₁,
        tauto,
        fconstructor,
        exact (n_n.add 1 : ℕ),
        suffices s : (b.transition_n t x₁ n_n) ∨ 
          (∃ c, (b.rest_utransition c) ∧ (c.transition_n t x₁ n_n)),
        tauto,
        suffices s : (∃ c, (b.rest_utransition c) ∧ 
          (c.transition_n t x₁ n_n)),
        tauto,
        fconstructor,
        exact a₂_h_w,
        tauto,
      },
    },
  },
end

lemma ccs.transition_psq_2 : ∀ (p q w p₁: ccs lab nam) (t : lab), 
  ccs.funcion2 q w p ∧ ccs.transition p t p₁ → ccs.transition w t p₁ 
  ∨ ccs.transition q t p₁ :=
begin
  intro x,
  intro a,
  intro b,
  intro x₁,
  intro t,
  assume a₁,
  cases a₁,
  have h₁ : ccs.funcion1 a b x → x = (b + a : ccs lab nam),
  tauto,
  have h₂ : x = (b + a : ccs lab nam),
  tauto,
  suffices s₁ : ccs.transition (b + a) t x₁ → ccs.transition b t x₁ ∨ 
    ccs.transition a t x₁,
  subst h₂,
  exact s₁ a₁_right,
  assume a₂,
  cases a₂,
  rename a₂_w n,
  induction n,
  {
    cases a₂_h,
    {
      suffices s : b.transition t x₁,
      tauto,
      fconstructor,
      exact 0,
      tauto,
    },
    {
      suffices s : a.transition t x₁,
      tauto,
      fconstructor,
      exact 0,
      tauto,
    },
  },
  {
    cases a₂_h,
    {
      exact n_ih a₂_h,
    },
    {
      cases a₂_h,
      cases a₂_h_h,
      cases a₂_h_h_left,
      {
        suffices s : b.transition t x₁,
        tauto,
        fconstructor,
        exact (n_n.add 1 : ℕ),
        suffices s : (b.transition_n t x₁ n_n) ∨ 
          (∃ c, (b.rest_utransition c) ∧ (c.transition_n t x₁ n_n)),
        tauto,
        suffices s : (∃ c, (b.rest_utransition c) ∧ 
          (c.transition_n t x₁ n_n)),
        tauto,
        fconstructor,
        exact a₂_h_w,
        tauto,
      },
      {
        suffices s : a.transition t x₁,
        tauto,
        fconstructor,
        exact (n_n.add 1 : ℕ),
        suffices s : (a.transition_n t x₁ n_n) ∨ 
          (∃ c, (a.rest_utransition c) ∧ (c.transition_n t x₁ n_n)),
        tauto,
        suffices s : (∃ c, (a.rest_utransition c) ∧ 
          (c.transition_n t x₁ n_n)),
        tauto,
        fconstructor,
        exact a₂_h_w,
        tauto,
      },
    },
  },
end

lemma ccs.transition_psq_left : ∀ (p q w : ccs lab nam) (t : lab), 
  ccs.transition p t w → ccs.transition (p + q) t w :=
begin
  intro x,
  intro y,
  intro z,
  intro t,
  assume a₁,
  cases a₁,
  rename a₁_w n,
  induction n,
  {
    suffices s : x.utransition t z,
    fconstructor,
    exact 0,
    fconstructor,
    tauto,
    tauto,
  },
  {
    cases a₁_h,
    {
      exact n_ih a₁_h,
    },
    {
      cases a₁_h,
      cases a₁_h_h,
      fconstructor,
      exact (n_n.add 1),
      suffices s : ((x+y).transition_n t z n_n) ∨ (∃ c, 
        ((x+y).rest_utransition c) ∧ (c.transition_n t z n_n)),
      tauto,
      suffices s : (∃ c, ((x+y).rest_utransition c) ∧ 
        (c.transition_n t z n_n)),
      tauto,
      fconstructor,
      exact a₁_h_w,
      split,
      fconstructor,
      tauto,
      tauto,
    },
  },
end

lemma ccs.transition_psq_right : ∀ (p q w : ccs lab nam) (t : lab), 
  ccs.transition q t w → ccs.transition (p + q) t w :=
begin
  intro x,
  intro y,
  intro z,
  intro t,
  assume a₁,
  cases a₁,
  rename a₁_w n,
  induction n,
  {
    suffices s : y.utransition t z,
    fconstructor,
    exact 0,
    suffices s₁ : (x.utransition t z) ∨ (y.utransition t z),
    tauto,
    tauto,
    tauto,
  },
  {
    cases a₁_h,
    {
      exact n_ih a₁_h,
    },
    {
      cases a₁_h,
      cases a₁_h_h,
      fconstructor,
      exact (n_n.add 1),
      suffices s : ((x+y).transition_n t z n_n) ∨ (∃ c, 
        ((x+y).rest_utransition c) ∧ (c.transition_n t z n_n)),
      tauto,
      suffices s : (∃ c, ((x+y).rest_utransition c) ∧ 
        (c.transition_n t z n_n)),
      tauto,
      fconstructor,
      exact a₁_h_w,
      split,
      suffices s : x.rest_utransition a₁_h_w ∨ y.rest_utransition a₁_h_w,
      tauto,
      tauto,
      tauto,
    },
  },
end

theorem ccs.property_psq_bisimilar : ∀ (p q w : ccs lab nam), 
  p ∼ q → (p + w) ∼ (q + w) ∧ (w + p) ∼ (w + q) := 
begin
  intro x,
  intro y,
  intro z,
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
            have h₃ : ∃ (w₁ : ccs lab nam), (ccs.transition j l w₁ ∧ 
              (r q₁ w₁)),
            exact ccs.bisimilar_left r a₁_h_right i j l q₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w w₁,
            fconstructor,
            exact w₁,
            split,
            {
              have h₄ : ccs.transition (j + k : ccs lab nam) l w₁,
              exact ccs.transition_psq_left j k w₁ l h₃_h_left,
              have h₅ : w = (j + k),
              tauto,
              subst h₅,
              exact h₄,
            },
            {
              suffices s₁ : relation.join_relations r 
                relation.identity_relation q₁ w₁, exact 
                relation.join_relations_right (relation.relation4 r 
                ccs.funcion1) (relation.join_relations r 
                relation.identity_relation) q₁ w₁ s₁,
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
            suffices s₁ : relation.join_relations r 
              relation.identity_relation q₁ q₁, exact 
              relation.join_relations_right (relation.relation4 r 
              ccs.funcion1) (relation.join_relations r 
              relation.identity_relation) q₁ q₁ s₁,
            have h₄ : relation.identity_relation q₁ q₁,
            tauto,
            exact relation.join_relations_right r 
              relation.identity_relation q₁ q₁ h₄,
          },
        },
        {
          cases a₂_left,
          {
            have h₁ : r q w,
            tauto,
            have h₂ : r q w ∧ ccs.transition q l q₁,
            tauto,
            have h₃ : ∃ (y₁ : ccs lab nam), w.transition l y₁ ∧ r q₁ y₁,
            exact ccs.bisimilar_left r a₁_h_right q w l q₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w w₁,
            fconstructor,
            exact w₁,
            split,
            tauto,
            have h₄ : relation.join_relations r relation.identity_relation 
              q₁ w₁,
            fconstructor,
            tauto,
            exact relation.join_relations_right (relation.relation4 r 
              ccs.funcion1) (relation.join_relations r 
              relation.identity_relation) q₁ w₁ h₄,
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
            have h₃ : relation.join_relations r relation.identity_relation 
              q₁ q₁, exact relation.join_relations_right r 
              relation.identity_relation q₁ q₁ h₂, exact 
              relation.join_relations_right (relation.relation4 r 
              ccs.funcion1) (relation.join_relations r 
              relation.identity_relation) q₁ q₁ h₃,
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
            have h₃ : ∃ (q₁ : ccs lab nam), (ccs.transition i l q₁ ∧ 
              (r q₁ w₁)),
            exact ccs.bisimilar_right r a₁_h_right i j l w₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w q₁,
            fconstructor,
            exact q₁,
            split,
            {
              have h₄ : ccs.transition (i + k : ccs lab nam) l q₁,
              exact ccs.transition_psq_left i k q₁ l h₃_h_left,
              have h₅ : q = (i + k),
              tauto,
              subst h₅,
              exact h₄,
            },
            {
              suffices s₁ : relation.join_relations r 
                relation.identity_relation q₁ w₁, exact 
                relation.join_relations_right (relation.relation4 r 
                ccs.funcion1) (relation.join_relations r 
                relation.identity_relation) q₁ w₁ s₁,
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
            suffices s₁ : relation.join_relations r 
              relation.identity_relation w₁ w₁,
            exact relation.join_relations_right (relation.relation4 r 
              ccs.funcion1) (relation.join_relations r 
              relation.identity_relation) w₁ w₁ s₁,
            have h₄ : relation.identity_relation w₁ w₁,
            tauto,
            exact relation.join_relations_right r 
              relation.identity_relation w₁ w₁ h₄,
          },
        },
        {
          cases a₂_left,
          {
            have h₁ : r q w,
            tauto,
            have h₂ : r q w ∧ ccs.transition w l w₁,
            tauto,
            have h₃ : ∃ (y₁ : ccs lab nam), q.transition l y₁ ∧ r y₁ w₁,
            exact ccs.bisimilar_right r a₁_h_right q w l w₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w q₁,
            fconstructor,
            exact q₁,
            split,
            tauto,
            have h₄ : relation.join_relations r relation.identity_relation 
              q₁ w₁,
            fconstructor,
            tauto,
            exact relation.join_relations_right (relation.relation4 r 
              ccs.funcion1) (relation.join_relations r 
              relation.identity_relation) q₁ w₁ h₄,
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
            have h₃ : relation.join_relations r relation.identity_relation 
              w₁ w₁,
            exact relation.join_relations_right r 
              relation.identity_relation w₁ w₁ h₂,
            exact relation.join_relations_right (relation.relation4 r 
              ccs.funcion1) (relation.join_relations r 
              relation.identity_relation) w₁ w₁ h₃,
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
            suffices s₁ : relation.join_relations r 
              relation.identity_relation q₁ q₁,
            exact relation.join_relations_right (relation.relation4 r 
              ccs.funcion2) (relation.join_relations r 
              relation.identity_relation) q₁ q₁ s₁,
            have h₄ : relation.identity_relation q₁ q₁,
            tauto,
            exact relation.join_relations_right r 
              relation.identity_relation q₁ q₁ h₄,
          },
          {
            have h₂ : r i j ∧ ccs.transition i l q₁,
            tauto,
            have h₃ : ∃ (w₁ : ccs lab nam), (ccs.transition j l w₁ ∧ 
              (r q₁ w₁)),
            exact ccs.bisimilar_left r a₁_h_right i j l q₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w w₁,
            fconstructor,
            exact w₁,
            split,
            {
              have h₄ : ccs.transition (k + j : ccs lab nam) l w₁,
              exact ccs.transition_psq_right k j w₁ l h₃_h_left,
              have h₅ : w = (k + j),
              tauto,
              subst h₅,
              exact h₄,
            },
            {
              suffices s₁ : relation.join_relations r 
                relation.identity_relation q₁ w₁,
              exact relation.join_relations_right (relation.relation4 r 
                ccs.funcion2) (relation.join_relations r 
                relation.identity_relation) q₁ w₁ s₁,
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
            have h₃ : ∃ (y₁ : ccs lab nam), w.transition l y₁ ∧ r q₁ y₁,
            exact ccs.bisimilar_left r a₁_h_right q w l q₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w w₁,
            fconstructor,
            exact w₁,
            split,
            tauto,
            have h₄ : relation.join_relations r relation.identity_relation 
              q₁ w₁,
            fconstructor,
            tauto,
            exact relation.join_relations_right (relation.relation4 r 
              ccs.funcion2) (relation.join_relations r 
              relation.identity_relation) q₁ w₁ h₄,
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
            have h₃ : relation.join_relations r relation.identity_relation 
              q₁ q₁, exact relation.join_relations_right r 
              relation.identity_relation q₁ q₁ h₂, exact 
              relation.join_relations_right (relation.relation4 r 
              ccs.funcion2) (relation.join_relations r 
              relation.identity_relation) q₁ q₁ h₃,
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
            suffices s₁ : relation.join_relations r 
              relation.identity_relation w₁ w₁,
            exact relation.join_relations_right (relation.relation4 r 
              ccs.funcion2) (relation.join_relations r 
              relation.identity_relation) w₁ w₁ s₁,
            have h₄ : relation.identity_relation w₁ w₁,
            tauto,
            exact relation.join_relations_right r 
              relation.identity_relation w₁ w₁ h₄,
          },
          {
            have h₂ : r i j ∧ ccs.transition j l w₁,
            tauto,
            have h₃ : ∃ (q₁ : ccs lab nam), (ccs.transition i l q₁ ∧ 
              (r q₁ w₁)),
            exact ccs.bisimilar_right r a₁_h_right i j l w₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w q₁,
            fconstructor,
            exact q₁,
            split,
            {
              have h₄ : ccs.transition (k + i : ccs lab nam) l q₁,
              exact ccs.transition_psq_right k i q₁ l h₃_h_left,
              have h₅ : q = (k + i),
              tauto,
              subst h₅,
              exact h₄,
            },
            {
              suffices s₁ : relation.join_relations r 
                relation.identity_relation q₁ w₁,
              exact relation.join_relations_right (relation.relation4 r 
                ccs.funcion2) (relation.join_relations r 
                relation.identity_relation) q₁ w₁ s₁,
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
            have h₃ : ∃ (y₁ : ccs lab nam), q.transition l y₁ ∧ r y₁ w₁,
            exact ccs.bisimilar_right r a₁_h_right q w l w₁ h₂,
            cases h₃,
            cases h₃_h,
            rename h₃_w q₁,
            fconstructor,
            exact q₁,
            split,
            tauto,
            have h₄ : relation.join_relations r relation.identity_relation 
              q₁ w₁,
            fconstructor,
            tauto,
            exact relation.join_relations_right (relation.relation4 r 
              ccs.funcion2) (relation.join_relations r 
              relation.identity_relation) q₁ w₁ h₄,
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
            have h₃ : relation.join_relations r relation.identity_relation 
              w₁ w₁,
            exact relation.join_relations_right r 
              relation.identity_relation w₁ w₁ h₂,
            exact relation.join_relations_right (relation.relation4 r 
              ccs.funcion2) (relation.join_relations r 
              relation.identity_relation) w₁ w₁ h₃,
          },
        },
      },
    }
  },
end

end ProcessAlgebra