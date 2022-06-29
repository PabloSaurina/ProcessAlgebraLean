import data.fintype.basic
import data.pfun
import logic.function.iterate
import order.basic
import tactic.apply_fun
import set_theory.cardinal


-- Definimos Labelled Transition System

universes u v

structure LTS (proc: Type u) (act: Type v) := 
(start: proc)
(f: proc → act → set proc)

namespace LTS

variables {proc: Type u} {act: Type v}
  (P : LTS proc act)

def transition: proc → act → set proc
|p a:=(P.f p a)

def exist_transition_from: proc → proc → Prop
|p q:= ∃ a, (q ∈ P.f p a)

def reaches_from: proc → proc → Prop :=
relation.refl_trans_gen (λ a b, P.exist_transition_from a b)

def reaches: proc → Prop
|q := P.reaches_from P.start q

def strong_bisimulation (r₁: proc → proc → Prop):= ∀ x y, (∀ a (x₁:proc), 
  (r₁ x y ∧ x₁ ∈ P.transition x a) → ∃ (y₁:proc), (y₁ ∈ P.transition y a 
  ∧ (r₁ x₁ y₁))) ∧ (∀ b (y₁:proc), (r₁ x y ∧ y₁ ∈ P.transition y b) → ∃ 
  (x₁:proc), (x₁ ∈ P.transition x b ∧ (r₁ x₁ y₁)))

def bisimilar (x:proc) (y:proc) := ∃ (s:proc → proc → Prop), 
  (s x y) ∧ P.strong_bisimulation s

def bisimilar_relation: proc → proc → Prop
|p q := P.bisimilar p q

end LTS 

-- Para las proximas demostraciones utilizaremos ciertas relaciones que hay que definir
-- previamente. Realizamos esto dentro del espacio 'relation'

namespace relation

variable {X: Type u}

def inverted_binary_relation (r:X → X → Prop) : X → X → Prop
|q p := r p q

def identity_relation : X → X → Prop
|q p := p = q

def relation1 (r:X → X → Prop) (s:X → X → Prop) : X → X → Prop 
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
|a b := (a,b) ∈ A

def join_relations (r:X → X → Prop) (s:X → X → Prop) : X → X → Prop
|a b := relation_conj (set.union (conj_relation r) (conj_relation s)) a b

end relation


-- Probamos ciertos reusltados sencillos

variables {proc act : Type u}

lemma lts.strong_bisimulation.identity_relation : ∀ (P:LTS proc act),
  P.strong_bisimulation relation.identity_relation :=
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
  assume h₁,
  suffices s₁ : ∃ (r : proc  → proc  → Prop), (r x y) ∧ P.strong_bisimulation r,
  {
    cases s₁,
    let r₁ := relation.inverted_binary_relation s₁_w,
    have h₂ : ∃ (r : proc  → proc  → Prop), (r y x) ∧ P.strong_bisimulation r,
    {
      have h₃ : (r₁ y x) ∧ P.strong_bisimulation r₁,
      {
        cases s₁_h,
        split,
        {
          from s₁_h_left,
        },
        {
          suffices s₂ : ∀ x y, (∀ a (x₁ : proc), (s₁_w x y ∧ x₁ ∈ P.transition x a) → 
          ∃ (y₁ : proc), (y₁ ∈ P.transition y a ∧ (s₁_w x₁ y₁))) ∧ (∀ b (y₁ : proc), 
          (s₁_w x y ∧ y₁ ∈ P.transition y b) → ∃ (x₁ : proc), (x₁ ∈ P.transition x b
          ∧ (s₁_w x₁ y₁))),
          {
            intro w,
            intro z,
            suffices s₃ : (∀ t (z₁ : proc), (s₁_w z w ∧ z₁ ∈ P.transition z t) → ∃ 
            (w₁ : proc), (w₁ ∈ P.transition w t ∧ (s₁_w z₁ w₁))) ∧ (∀ t (w₁ : proc), 
            (s₁_w z w ∧ w₁ ∈ P.transition w t) → ∃ (z₁ : proc), (z₁ ∈ P.transition z 
            t ∧ (s₁_w z₁ w₁))),
            {
              cases s₃,
              split,
              {
                intro t,
                intro w₁,
                assume h₂,
                suffices s₄ : s₁_w z w ∧ w₁ ∈ P.transition w t,
                {
                  suffices s₅ : s₁_w z w ∧ w₁ ∈ P.transition w t → 
                  (∃ (z₁ : proc), z₁ ∈ P.transition z t ∧ s₁_w z₁ w₁),
                  {
                    suffices s₆ : (∃ (z₁ : proc), z₁ ∈ P.transition z t ∧ s₁_w z₁ w₁),
                    {
                      cases s₆,
                      rename s₆_w z₁,
                      have h₃ : z₁ ∈ P.transition z t ∧ r₁ w₁ z₁,
                      {
                        from s₆_h,
                      },
                      {
                        split,
                        from h₃,
                      },
                    },
                    {
                      from s₅ s₄,
                    },
                  },
                  {
                    from s₃_right t w₁,
                  },
                },
                {
                  from h₂,
                }
              },
              {
                intro t,
                intro z₁,
                assume h₂,
                suffices s₄ : s₁_w z w ∧ z₁ ∈ P.transition z t,
                {
                  suffices s₅ : s₁_w z w ∧ z₁ ∈ P.transition z t → 
                  (∃ (w₁ : proc), w₁ ∈ P.transition w t ∧ s₁_w z₁ w₁),
                  {
                    suffices s₆ : (∃ (w₁ : proc), w₁ ∈ P.transition w t ∧ s₁_w z₁ w₁),
                    {
                      cases s₆,
                      rename s₆_w w₁,
                      have h₃ : w₁ ∈ P.transition w t ∧ r₁ w₁ z₁,
                      {
                        from s₆_h,
                      },
                      {
                        split,
                        from h₃,
                      },
                    },
                    {
                      from s₅ s₄,
                    },
                  },
                  {
                    from s₃_left t z₁,
                  },
                },
                {
                  from h₂,
                },
              },
            },
            {
              from s₂ z w,
            },
          },
          {
            from s₁_h_right,
          }
        },
      },
      {
        split,
        from h₃,
      },
    },
    {
      from h₂,
    },
  },
  {
    from h₁,
  },
end

theorem lts.bismilar_relation.equivalence: ∀ (P₁: LTS proc act), equivalence 
  (P₁.bisimilar_relation) :=
begin
  intro P,
  split,
  {
    intro p,
    let r : (proc → proc → Prop) := relation.identity_relation,
    have h₁ : P.bisimilar p p,
    {
      have h₂ : ∃(s : proc → proc → Prop), (s p p) ∧ P.strong_bisimulation s,
      {
        suffices s₁ : r p p,
        {
          suffices s₂ : P.strong_bisimulation r,
          {
            suffices s₃ : r p p ∧ P.strong_bisimulation r,
            {
              fconstructor,
              assumption,
              from s₃,
            },
            {
              split,
              from s₁,
              from s₂,
            },
          },
          {
            have h₁ : ∀ x y, (∀ a (x₁ : proc), (r x y ∧ x₁ ∈ P.transition x a) → ∃ 
            (y₁ : proc), (y₁ ∈ P.transition y a ∧ (r x₁ y₁))) ∧ (∀ b (y₁ : proc), 
            (r x y ∧ y₁ ∈ P.transition y b) → ∃ (x₁ : proc), (x₁ ∈ P.transition x b 
            ∧ (r x₁ y₁))),
            {
              intro x,
              intro y,
              split,
              {
                intro t,
                intro z,
                assume a₁,
                cases a₁,
                suffices s₂ : x = y,
                {
                  have h₁ : z ∈ P.transition y t ∧ r z z,
                  {
                    split,
                    {
                      finish,
                    },
                    {
                      fconstructor,
                    },
                  },
                  {
                    finish,
                  },
                },
                {
                  have h₁ : ∀ a b, r a b → a = b,
                  {
                    tauto,
                  },
                  {
                    finish,
                  },
                },
              },
              {
                intro t,
                intro z,
                assume a₁,
                cases a₁,
                suffices s₂ : x = y,
                {
                  have h₁ : z ∈ P.transition x t ∧ r z z,
                  {
                    split,
                    {
                      finish,
                    },
                    {
                      fconstructor,
                    },
                  },
                  {
                    finish,
                  },
                },
                {
                  have h₁ : ∀ a b, r a b → a = b,
                  {
                    tauto,
                  },
                  {
                    finish,
                  },
                },
              },
            },
            {
              from h₁,
            },
          },
        },
        {
          fconstructor,
        },
      },
      {
        from h₂,
      },
    },
    {
      from h₁,
    },
  },
  {split,
  {
    intro p,
    intro q,
    assume h,
    have h₁ : P.bisimilar p q,
    {
      from h,
    },
    {
      suffices s : P.bisimilar q p,
      {
        from s,
      },
      {
        have h₂ : symmetric P.bisimilar,
        {
          from lts.bisimilar.symmetric P,
        },
        {
          exact h₂ h₁,
        },
      },
    },
  },
  {
    intro x,
    intro y,
    intro z,
    assume h₁,
    assume h₂,
    cases h₁,
    cases h₂,
    let r : (proc → proc → Prop):=  relation.relation1 h₁_w h₂_w,
    have h₃ : P.bisimilar x z,
    {
      have h₄ : ∃ (s : proc → proc → Prop), (s x z) ∧ P.strong_bisimulation s,
      {
        fconstructor,
        exact r,
        split,
        {
          fconstructor,
          exact y,
          split,
          cases h₁_h,
          exact h₁_h_left,
          cases h₂_h,
          exact h₂_h_left,
        },
        {
          intro a,
          intro c,
          split,
          {
            intro t,
            intro a₁,
            assume h₂,
            cases h₂,
            suffices s₁ : ∃ b, h₁_w a b ∧ h₂_w b c,
            {
              cases h₁_h,
              cases h₂_h,
              cases s₁,
              rename s₁_w b,
              suffices s₂ : ∃ b₁ : proc, b₁ ∈ P.transition b t ∧ h₁_w a₁ b₁,
              {
                cases s₂,
                rename s₂_w b₁,
                suffices s₃ : ∃ c₁ : proc, c₁ ∈ P.transition c t ∧ h₂_w b₁ c₁,
                {
                  cases s₃,
                  rename s₃_w c₁,
                  fconstructor,
                  exact c₁,
                  split,
                  cases s₃_h,
                  from s₃_h_left,
                  cases s₂_h,
                  cases s₃_h,
                  fconstructor,
                  exact b₁,
                  split,
                  from s₂_h_right,
                  from s₃_h_right,
                },
                {
                  cases s₁_h,
                  suffices s₄ : (∀ t (x₁ : proc),(h₂_w b c ∧ x₁ ∈ P.transition b 
                  t) → ∃ (y₁ : proc), (y₁ ∈ P.transition c t ∧ (h₂_w x₁ y₁))) 
                  ∧ (∀ t (y₁ : proc), (h₂_w b c ∧ y₁ ∈ P.transition c t) → ∃ (x₁ : proc),
                  (x₁ ∈ P.transition b t ∧ (h₂_w x₁ y₁))),
                  {
                    suffices s₅ : (h₂_w b c ∧ b₁ ∈ P.transition b t) → ∃ (y₁ : proc),
                    (y₁ ∈ P.transition c t ∧ (h₂_w b₁ y₁)),
                    {
                      have h₃ : h₂_w b c ∧ b₁ ∈ P.transition b t,
                      {
                        split,
                        from s₁_h_right,
                        cases s₂_h,
                        from s₂_h_left,
                      },
                      {
                        from s₅ h₃,
                      },
                    },
                    {
                      cases s₄,
                      from s₄_left t b₁,
                    },
                  },
                  {
                    from h₂_h_right b c,
                  },
                },
              },
              {
                cases s₁_h,
                suffices s₃ : (∀ t (x₁ : proc),(h₁_w a b ∧ x₁ ∈ P.transition a 
                t) → ∃ (y₁ : proc), (y₁ ∈ P.transition b t ∧ (h₁_w x₁ y₁))) 
                ∧ (∀ t (y₁ : proc), (h₁_w a b ∧ y₁ ∈ P.transition b t) → ∃ (x₁ : proc),
                (x₁ ∈ P.transition a t ∧ (h₁_w x₁ y₁))),
                {
                  suffices s₄ : (h₁_w a b ∧ a₁ ∈ P.transition a t) → ∃ (y₁ : proc), 
                  (y₁ ∈ P.transition b t ∧ (h₁_w a₁ y₁)),
                  {
                    have h₃ : h₁_w a b ∧ a₁ ∈ P.transition a t,
                    {
                      split,
                      from s₁_h_left,
                      from h₂_right,
                    },
                    {
                      from s₄ h₃,
                    },
                  },
                  {
                    cases s₃,
                    from s₃_left t a₁,
                  },
                },
                {
                  from h₁_h_right a b,
                },
              },
            },
            {
              tauto,
            },
          },
          {
            intro t,
            intro c₁,
            assume h₂,
            cases h₂,
            suffices s₁ : ∃ b, h₁_w a b ∧ h₂_w b c,
            {
              cases h₁_h,
              cases h₂_h,
              cases s₁,
              rename s₁_w b,
              suffices s₂ : ∃ b₁ : proc, b₁ ∈ P.transition b t ∧ h₂_w b₁ c₁,
              {
                cases s₂,
                rename s₂_w b₁,
                suffices s₃ : ∃ a₁ : proc, a₁ ∈ P.transition a t ∧ h₁_w a₁ b₁,
                {
                  cases s₃,
                  rename s₃_w a₁,
                  fconstructor,
                  exact a₁,
                  split,
                  cases s₃_h,
                  from s₃_h_left,
                  cases s₂_h,
                  cases s₃_h,
                  fconstructor,
                  exact b₁,
                  split,
                  from s₃_h_right,
                  from s₂_h_right,
                },
                {
                  cases s₁_h,
                  suffices s₄ : (∀ t (x₁ : proc),(h₁_w a b ∧ x₁ ∈ P.transition a 
                  t) → ∃ (y₁ : proc), (y₁ ∈ P.transition b t ∧ (h₁_w x₁ y₁))) 
                  ∧ (∀ t (y₁ : proc), (h₁_w a b ∧ y₁ ∈ P.transition b t) → ∃ (x₁ : proc),
                  (x₁ ∈ P.transition a t ∧ (h₁_w x₁ y₁))),
                  {
                    suffices s₅ : (h₁_w a b ∧ b₁ ∈ P.transition b t) → ∃ (y₁ : proc),
                    (y₁ ∈ P.transition a t ∧ (h₁_w y₁ b₁)),
                    {
                      have h₃ : h₁_w a b ∧ b₁ ∈ P.transition b t,
                      {
                        split,
                        from s₁_h_left,
                        cases s₂_h,
                        from s₂_h_left,
                      },
                      {
                        from s₅ h₃,
                      },
                    },
                    {
                      cases s₄,
                      from s₄_right t b₁,
                    },
                  },
                  {
                    from h₁_h_right a b,
                  },
                },
              },
              {
                cases s₁_h,
                suffices s₃ : (∀ t (x₁ : proc),(h₂_w b c ∧ x₁ ∈ P.transition b 
                t) → ∃ (y₁ : proc), (y₁ ∈ P.transition c t ∧ (h₂_w x₁ y₁))) 
                ∧ (∀ t (y₁ : proc), (h₂_w b c ∧ y₁ ∈ P.transition c t) → ∃ (x₁ : proc),
                (x₁ ∈ P.transition b t ∧ (h₂_w x₁ y₁))),
                {
                  suffices s₄ : (h₂_w b c ∧ c₁ ∈ P.transition c t) → ∃ (y₁ : proc), 
                  (y₁ ∈ P.transition b t ∧ (h₂_w y₁ c₁)),
                  {
                    have h₃ : h₂_w b c ∧ c₁ ∈ P.transition c t,
                    {
                      split,
                      from s₁_h_right,
                      from h₂_right,
                    },
                    {
                      from s₄ h₃,
                    },
                  },
                  {
                    cases s₃,
                    from s₃_right t c₁,
                  },
                },
                {
                  from h₂_h_right b c,
                },
              },
            },
            {
              tauto,
            },
          },
        },
      },
      {
        from h₄,
      },
    },
    {
      exact h₃,
    },
  },
  },
end

theorem lts.bisimilar_relation.is_strong_bisimulation : ∀ (P: LTS proc act), P.strong_bisimulation 
  P.bisimilar_relation :=
begin
  intro P,
  let r := P.bisimilar_relation,
  suffices s₁ : P.strong_bisimulation r,
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
        have s₄ : ∃ (s : proc → proc → Prop), s x y ∧ P.strong_bisimulation s,
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
            have s₅ : (∀ a (x₁ : proc), (s x y ∧ x₁ ∈ P.transition x a) → ∃ (y₁ : proc), 
            (y₁ ∈ P.transition y a ∧ (s x₁ y₁))) ∧ (∀ b (y₁ : proc), (s x y ∧ y₁ ∈ P.transition y b) 
            → ∃ (x₁ : proc), (x₁ ∈ P.transition x b ∧ (s x₁ y₁))),
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
        have s₄ : ∃ (s : proc → proc → Prop), s x y ∧ P.strong_bisimulation s,
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
            have s₅ : (∀ a (x₁ : proc), (s x y ∧ x₁ ∈ P.transition x a) → ∃ (y₁ : proc), 
            (y₁ ∈ P.transition y a ∧ (s x₁ y₁))) ∧ (∀ b (y₁ : proc), (s x y ∧ y₁ ∈ P.transition y b) 
            → ∃ (x₁ : proc), (x₁ ∈ P.transition x b ∧ (s x₁ y₁))),
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

lemma lts.bisimilar_relation.supset.strong_bisimulation : ∀ (P:LTS proc act), ∀ 
  (r:proc → proc → Prop), P.strong_bisimulation r → (∀ x y, r x y → P.bisimilar_relation x y) :=
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

theorem lts.bisimilar_relation.is_largest_strong_bisimulation : ∀ (P₁: LTS proc act) 
  (r₁:proc → proc → Prop), P₁.strong_bisimulation r₁ → (cardinal.mk 
  (relation.conj_relation P₁.bisimilar_relation)) >= (cardinal.mk (relation.conj_relation r₁)) :=
begin
  intro P,
  let r := P.bisimilar_relation,
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

theorem lts.bisimilar_relation.property : ∀ (P : LTS proc act) (x y : proc), ( ( ∀ (t : act) 
  (x₁ : proc), x₁ ∈ P.transition x t → ∃ (y₁ : proc), y₁ ∈ P.transition y t ∧ 
  P.bisimilar_relation x₁ y₁ ) ∧ ( ∀ (t : act) (y₁ : proc), y₁ ∈ P.transition y t → ∃ (x₁ : proc),
  x₁ ∈ P.transition x t ∧ P.bisimilar_relation x₁ y₁ ) ) → P.bisimilar_relation x y :=
begin 
  intro P,
  intro x,
  intro y,
  assume s₁,
  cases s₁,
  let r := relation.join_relations (relation.relation2 x y) P.bisimilar_relation,
  let con_r := (set.union (relation.conj_relation (relation.relation2 x y)) 
  (relation.conj_relation P.bisimilar_relation)),
  suffices s₂ : P.strong_bisimulation r,
  {
    have s₃ : r x y,
    {
      fconstructor,
      split,
      trivial,
      trivial,
    },
    {
      from lts.bisimilar_relation.supset.strong_bisimulation P r s₂ x y s₃,
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
      have h : P.bisimilar_relation a₁ a₁,
      fconstructor,
      exact relation.identity_relation,
      split,
      tauto,
      from lts.strong_bisimulation.identity_relation P,
      suffices h₁ : (a₁,a₁) ∈ con_r,
      tauto,
      suffices h₂ : (a₁,a₁)∈ (relation.conj_relation P.bisimilar_relation),
      exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h,
      fconstructor,
      exact relation.identity_relation,
      split,
      tauto,
      from lts.strong_bisimulation.identity_relation P,
      cases c₂,
      have h : ∃(b₁ : proc), b₁ ∈ P.transition y t ∧ P.bisimilar_relation a₁ b₁,
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
      exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h_h_right,
      cases c₂,
      suffices h : (a,b) ∈ (relation.conj_relation P.bisimilar_relation),
      have h₁ : P.bisimilar_relation a b,
      tauto,
      have h₂ : ∃ (s : proc → proc → Prop), (s a b) ∧ P.strong_bisimulation s,
      from h₁,
      cases h₂,
      rename h₂_w s,
      cases h₂_h,
      have h₃ : (∀ t (a₁ : proc), (s a b ∧ a₁ ∈ P.transition a t) → ∃ (y₁ : proc), 
        (y₁ ∈ P.transition b t ∧ (s a₁ y₁))) ∧ (∀ t (y₁ : proc), (s a b ∧ y₁ ∈ P.transition 
        b t) → ∃ (a₁ : proc), (a₁ ∈ P.transition a t ∧ (s a₁ y₁))),
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
      exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₆,
      have h₁ : P.bisimilar_relation a b,
      have h₂ : r a b → (a = x ∧ b = y) ∨ P.bisimilar_relation a b,
      exact (set.mem_union (a, b) (relation.conj_relation (relation.relation2 x y))
        (relation.conj_relation (LTS.bisimilar_relation P))).mp,
      have h₃ : (a = x ∧ b = y) ∨ P.bisimilar_relation a b,
      from h₂ s₂_left,
      tauto,
      from h₁,
      have h₁ : r a b → (a = x ∧ b = y) ∨ P.bisimilar_relation a b,
      exact (set.mem_union (a, b) (relation.conj_relation (relation.relation2 x y))
        (relation.conj_relation (LTS.bisimilar_relation P))).mp,
      have h₂ : (a = x ∧ b = y) ∨ P.bisimilar_relation a b,
      from h₁ s₂_left,
      have h₃ : P.bisimilar_relation a b,
      tauto,
      have h₄ : ∃ (s : proc → proc → Prop), (s a b) ∧ P.strong_bisimulation s,
      from h₃,
      cases h₄,
      rename h₄_w s,
      cases h₄_h,
      have h₅ : (∀ t (a₁ : proc), (s a b ∧ a₁ ∈ P.transition a t) → ∃ (y₁ : proc), 
        (y₁ ∈ P.transition b t ∧ (s a₁ y₁))) ∧ (∀ t (y₁ : proc), (s a b ∧ y₁ ∈ P.transition 
        b t) → ∃ (a₁ : proc), (a₁ ∈ P.transition a t ∧ (s a₁ y₁))),
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
      exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₈,
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
      have h : P.bisimilar_relation b₁ b₁,
      fconstructor,
      exact relation.identity_relation,
      split,
      tauto,
      from lts.strong_bisimulation.identity_relation P,
      suffices h₁ : (b₁,b₁) ∈ con_r,
      tauto,
      suffices h₂ : (b₁,b₁) ∈ (relation.conj_relation P.bisimilar_relation),
      exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h,
      fconstructor,
      exact relation.identity_relation,
      split,
      tauto,
      from lts.strong_bisimulation.identity_relation P,
      cases c₂,
      have h : ∃ (a₁ : proc), a₁ ∈ P.transition x t ∧ P.bisimilar_relation a₁ b₁,
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
      exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h_h_right,
      cases c₂,
      suffices h : (a,b) ∈ (relation.conj_relation P.bisimilar_relation),
      have h₁ : P.bisimilar_relation a b,
      tauto,
      have h₂ : ∃ (s : proc → proc → Prop), (s a b) ∧ P.strong_bisimulation s,
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
      exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₆,
      have h₁ : P.bisimilar_relation a b,
      have h₂ : r a b → (a = x ∧ b = y) ∨ P.bisimilar_relation a b,
      exact (set.mem_union (a, b) (relation.conj_relation (relation.relation2 x y))
        (relation.conj_relation (LTS.bisimilar_relation P))).mp,
      have h₃ : (a = x ∧ b = y) ∨ P.bisimilar_relation a b,
      from h₂ s₂_left,
      tauto,
      from h₁,
      have h₁ : r a b → (a = x ∧ b = y) ∨ P.bisimilar_relation a b,
      exact (set.mem_union (a, b) (relation.conj_relation (relation.relation2 x y))
        (relation.conj_relation (LTS.bisimilar_relation P))).mp,
      have h₂ : (a = x ∧ b = y) ∨ P.bisimilar_relation a b,
      from h₁ s₂_left,
      have h₃ : P.bisimilar_relation a b,
      tauto,
      have h₄ : ∃ (s : proc → proc → Prop), (s a b) ∧ P.strong_bisimulation s,
      from h₃,
      cases h₄,
      rename h₄_w s,
      cases h₄_h,
      have h₅ : (∀ t (y₁ : proc), (s a b ∧ y₁ ∈ P.transition a t) → ∃ (b₁ : proc), 
        (b₁ ∈ P.transition b t ∧ (s y₁ b₁))) ∧ (∀ t (b₁ : proc), (s a b ∧ b₁ ∈ P.transition 
        b t) → ∃ (y₁ : proc), (y₁ ∈ P.transition a t ∧ (s y₁ b₁))),
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
      exact (relation.conj_relation (relation.relation2 x y)).mem_union_right h₈,
    },
  },
end
