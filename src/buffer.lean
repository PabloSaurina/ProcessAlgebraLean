import data.fintype.basic
import data.pfun
import logic.function.iterate
import order.basic
import tactic.apply_fun
import set_theory.cardinal
import data.fin.tuple
import ProcessAlgebra
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
--------------------------------     LTS × CCS     --------------------------------
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------

namespace lts_ccs

-- Definimos Buffer₀¹

def buffer1_fun : string → string → set string
|"B₀" "in" := {"B₁"} 
|"B₁" "out" := {"B₀"} 
|_ _ := {}

def buffer1 : LTS string string := LTS.mk "B₀" buffer1_fun


-- Definimos Buffer₀² como B₀¹|B₀¹ y como B₀²

def buffer2_1_fun : string → string → set string
|"B₀B₀" "in" := {"B₁B₀","B₀B₁"} 
|"B₁B₁" "out" := {"B₀B₁","B₁B₀"}
|"B₁B₀" "in" := {"B₁B₁"}
|"B₀B₁" "in" := {"B₁B₁"}
|"B₁B₀" "out" := {"B₀B₀"}
|"B₀B₁" "out" := {"B₀B₀"}
|_ _ := {}

def buffer2_1 : LTS string string := LTS.mk "B₀B₀" buffer2_1_fun

def buffer2_2_fun : string → string → set string
|"B₀" "in" := {"B₁"} 
|"B₁" "out" := {"B₀"}
|"B₁" "in" := {"B₂"}
|"B₂" "out" := {"B₁"}
|_ _ := {}

def buffer2_2 : LTS string string := LTS.mk "B₀" buffer2_2_fun

def buffer2 : LTS string string := LTS.union_lts buffer2_1 buffer2_2

end lts_ccs 

namespace relation

variable {X: Type u}

def buffer2_relation_conj : set (string × string) := {("B₀","B₀B₀"),
  ("B₁","B₁B₀"),("B₁","B₀B₁"),("B₂","B₁B₁")}

def buffer2_relation : string → string → Prop :=
  relation_conj buffer2_relation_conj

def binary_x (S :set (X × X)) : set X
|a := ∃ b, (a,b) ∈ S

end relation

variable {X: Type u}

lemma relation_aux :∀ (S: set (X × X)), ∀ (x y : X), x ∉ (relation.binary_x S) → 
  (x,y) ∉ S :=
begin
  intro S,
  intro,
  intro,
  assume a,
  suffices s : ∀ b, (x,b) ∉ S,
  tauto,
  by_contradiction,
  have h₁ : ∃ b, (x,b)∈ S,
  finish,
  contradiction,
end

lemma buffer2_relation_x_l1 : ∀ y, y ∈ relation.binary_x relation.buffer2_relation_conj → 
  y ∈ ({"B₀","B₁","B₂"} : set string) := 
begin
  intro,
  assume a,
  have h₃ : relation.buffer2_relation_conj = {("B₀","B₀B₀"),("B₁","B₁B₀"),("B₁","B₀B₁"),
    ("B₂","B₁B₁")},
  tauto,
  have h₄ : ∃ b, (y,b) ∈ ({("B₀","B₀B₀"),("B₁","B₁B₀"),("B₁","B₀B₁"),("B₂","B₁B₁")} : 
    set (string × string)),
  tauto,
  cases h₄,
  have h₅ : (y,h₄_w) = ("B₀","B₀B₀") ∨ (y,h₄_w) ∈ ({("B₁","B₁B₀"),("B₁","B₀B₁"),("B₂","B₁B₁")} : 
    set (string × string)),
  tauto,
  cases h₅,
  {
    finish,
  },
  {
    have h₆ : (y,h₄_w) = ("B₁","B₁B₀") ∨ (y,h₄_w) ∈ ({("B₁","B₀B₁"),("B₂","B₁B₁")} : 
      set (string × string)),
    from h₅,
    cases h₆,
    {
      finish,
    },
    {
      have h₇ : (y,h₄_w) = ("B₁","B₀B₁") ∨ (y,h₄_w) ∈ ({("B₂","B₁B₁")} : 
        set (string × string)),
      from h₆,
      cases h₇,
      {
        finish,
      },
      {
        have h₈ : (y,h₄_w) = ("B₂","B₁B₁"),
        from h₇,
        finish,
      },
    },
  },
end

lemma buffer2_relation_x_l2 : ∀ y, y ∈ ({"B₀","B₁","B₂"} : set string) → y ∈ 
  relation.binary_x relation.buffer2_relation_conj := 
begin
  intro y,
  assume a,
  have h₁ : y = "B₀" ∨ y ∈ ({"B₁","B₂"} : set string),
  tauto,
  have h₂ : y = "B₀" ∨ y = "B₁" ∨ y ∈ ({"B₂"} : set string),
  tauto,
  have h : y = "B₀" ∨ y = "B₁" ∨ y = "B₂",
  tauto,
  suffices s₁ : y ∈ relation.binary_x ({("B₀","B₀B₀"),("B₁","B₁B₀"),("B₁","B₀B₁"),
    ("B₂","B₁B₁")} : set (string × string)),
  tauto,
  cases h,
  {
    let b := "B₀B₀",
    fconstructor,
    exact b,
    fconstructor,
    tauto,
  },
  {
    cases h,
    {
      let b := "B₁B₀",
      fconstructor,
      exact b,
      have h₃ : (y,b) ∈ set.union ({("B₀","B₀B₀")} : set (string × string)) ({("B₁","B₁B₀"),
        ("B₁","B₀B₁"),("B₂","B₁B₁")} : set (string × string)),
      {
        have h₄ : (y,b) ∈ ({("B₁","B₁B₀"),("B₁","B₀B₁"),("B₂","B₁B₁")} : set (string × string)),
        fconstructor,
        tauto,
        exact set.mem_union_right ({("B₀","B₀B₀")} : set (string × string)) h₄,
      },
      tauto,
    },
    {
      let b := "B₁B₁",
      fconstructor,
      exact b,
      have h₃ : (y,b) ∈ set.union ({("B₂","B₁B₁")} : set (string × string)) ({("B₀","B₀B₀"),
        ("B₁","B₁B₀"),("B₁","B₀B₁")} : set (string × string)),
      {
        fconstructor,
        tauto,
      },
      {
        finish,
      },
    },
  },
end

lemma buffer2_relation_x : relation.binary_x relation.buffer2_relation_conj = 
  ({"B₀","B₁","B₂"} : set string) :=
begin
  have h₁ : ∀ y, y ∈ relation.binary_x relation.buffer2_relation_conj → y ∈ ({"B₀","B₁","B₂"} : 
    set string),
  {
    exact buffer2_relation_x_l1,
  },
  {
    have h₂ : ∀ y, y ∈ {"B₀","B₁","B₂"} → y ∈ relation.binary_x relation.buffer2_relation_conj,
    {
      exact buffer2_relation_x_l2,
    },
    {
      exact le_antisymm h₁ h₂,
    },
  }
end

theorem lts.buffer2_equivalence : lts_ccs.buffer2.strong_bisimilarity "B₀" "B₀B₀" :=
begin
  let r := relation.buffer2_relation,
  fconstructor,
  exact r,
  split,
  {
    fconstructor,
    triv,
  },
  {
    intro,
    intro,
    split,
    {
      intro,
      intro,
      assume a,
      cases a,
      have h₁ : relation.buffer2_relation x y → (x,y) = ("B₀","B₀B₀") ∨ (x,y) = ("B₁","B₁B₀")
        ∨ (x,y) = ("B₁","B₀B₁") ∨ (x,y) = ("B₂","B₁B₁"),
      {
        assume a₁,
        have h₂ : relation.buffer2_relation x y → (x,y) ∈ relation.buffer2_relation_conj,
        tauto,
        have h₃ : (x,y) ∈ relation.buffer2_relation_conj,
        exact h₂ a₁,
        have h₄ : (x,y) ∈ relation.buffer2_relation_conj → (x,y) ∈ {("B₀","B₀B₀"),
          ("B₁","B₁B₀"),("B₁","B₀B₁"),("B₂","B₁B₁")},
        tauto,
        sorry, -- finish,
      },
      {
        have h₂ : (x,y) = ("B₀","B₀B₀") ∨ (x,y) = ("B₁","B₁B₀") ∨ (x,y) = ("B₁","B₀B₁") 
          ∨ (x,y) = ("B₂","B₁B₁"),
        from h₁ a_left,
        cases h₂,
        {
          let y₁ := "B₁B₀",
          fconstructor,
          exact y₁,
          have h₃ : a = "in",
          {
            suffices s₁ : ∀ a, lts_ccs.buffer2.transition x a ≠ ∅ → a = "in",
            {
              suffices s₂ : lts_ccs.buffer2.transition x a ≠ ∅,
              from s₁ a s₂,
              suffices s₃ : ∃ x₁, x₁ ∈ lts_ccs.buffer2.transition x a,
              sorry,
            },
            {
              sorry,
            },
          },
          {
            sorry,
          },
        },
        {
          sorry,
        },
      },

      -- have h : relation.buffer2_relation x y → (x = "B₀" ∨ x = "B₁" ∨ x ="B₂"),
      -- -- Esto hay que cambiarlo a por pares, que es mas sencillo.
      -- {
      --   assume a₁,
      --   by_contradiction,
      --   suffices s : r x y = ff,
      --   tauto,
      --   suffices s₁ : (x,y) ∉ relation.conj_relation r,
      --   exact congr_fun (false.rec (r x = λ (y : string), ↥ff) (s₁ a_left)) y,
      --   suffices s₂ : x ∉ relation.binary_x (relation.conj_relation r),
      --   exact relation_aux (relation.conj_relation r) x y s₂,
      --   have h₁ : relation.conj_relation r = relation.buffer2_relation_conj,
      --   {
      --     have h₂ : ∀ p q, (p,q) ∈ relation.conj_relation r → r p q,
      --     {
      --       intro,
      --       intro,
      --       assume a₂,
      --       sorry, -- finish,
      --     },
      --     {
      --       have h₃ : ∀ p q, r p q → relation.buffer2_relation p q,
      --       tauto,
      --       have h₄ : ∀ p q, relation.buffer2_relation p q → (p,q) ∈ 
      --         relation.buffer2_relation_conj,
      --       tauto,
      --       have h₅ : ∀ (p q : string), (p,q) ∈ relation.conj_relation r → 
      --         (p,q) ∈ relation.buffer2_relation_conj,
      --       {
      --         tauto,
      --       },
      --       {
      --         have h₆ : ∀ (p q : string), (p,q) ∈ relation.buffer2_relation_conj → 
      --         (p,q) ∈ relation.conj_relation r,
      --         {
      --           tauto,
      --         },
      --         {
      --           refine set.ext _,
      --           intro,
      --           cases x_1,
      --           split,
      --           from h₅ x_1_fst x_1_snd,
      --           from h₆ x_1_fst x_1_snd,
      --         },
      --       },
      --     },
      --   },
      --   {
      --     suffices s : x ∉ relation.binary_x relation.buffer2_relation_conj,
      --     tauto,
      --     suffices s : relation.binary_x relation.buffer2_relation_conj = {"B₀","B₁","B₂"},
      --     finish,
      --     exact buffer2_relation_x,
      --   },
      -- },
      -- {
      --   sorry,
      -- },
    },
    {
      sorry,
    },
  },
end

lemma lts.buffer2_equivalence_1 : ∀ a x, x ∈ lts_ccs.buffer2.transition "B₀" a → x = "B₁" :=
begin
  intro,
  intro,
  assume a₁,
  cases a₁,
  {
    sorry,
  },
  {
    suffices s₁ : x ∈ lts_ccs.buffer2_2_fun "B₀" a → x = "B₁",
    finish,
  },
end



end ProcessAlgebra