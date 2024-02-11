open import MLTT renaming (_×_ to _∧_ ; _+_ to _∨_)

module Logica where
    
    module Notacion where
        variable
            A B C P Q R : 𝓤₀ ̇
        
        ⊥ = 𝟘
        ⊤ = 𝟙
    open Notacion

    π₁ : A ∧ B → A
    π₁ ⟨ a , b ⟩ = a

    π₂ : A ∧ B → B
    π₂ ⟨ a , b ⟩ = b

    ¬_ : 𝓤₀  ̇ → 𝓤₀  ̇
    ¬ P = P → ⊥

    infixl 3 ¬_

    ∧-conmuta : (A ∧ B) → (B ∧ A)
    ∧-conmuta ⟨ a , b ⟩ = ⟨ b , a ⟩

    negacion-disjuncion-implica-conjuncion-de-negaciones : ¬ (A ∨ B) → ¬ A ∧ ¬ B
    negacion-disjuncion-implica-conjuncion-de-negaciones ¬[a∨b] = 
        ⟨ (λ a → ¬[a∨b] (inl a)) , (λ b → ¬[a∨b] (inr b)) ⟩

    conjuncion-negaciones-implica-negacion-disjuncion : (¬ A) ∧ (¬ B) → ¬ (A ∨ B)
    conjuncion-negaciones-implica-negacion-disjuncion [¬a∧¬b] (inl a) = ¬a a
        where
            ¬a = π₁ [¬a∧¬b]
    conjuncion-negaciones-implica-negacion-disjuncion [¬a∧¬b] (inr b) = ¬b b
        where
            ¬b = π₂ [¬a∧¬b]
    
    disjuncion-negaciones-implica-negacion-conjuncion : (¬ A) ∨ (¬ B) → ¬ (A ∧ B)
    disjuncion-negaciones-implica-negacion-conjuncion (inl ¬a) a∧b = ¬a (π₁ a∧b)
    disjuncion-negaciones-implica-negacion-conjuncion (inr ¬b) a∧b = ¬b (π₂ a∧b)

    proposicion-implica-su-doble-negacion : P → ¬ (¬ P)
    proposicion-implica-su-doble-negacion p ¬p = ¬p p

    nn-tercer-excluido : ¬ ¬ (A ∨ ¬ A)
    nn-tercer-excluido ¬[a∨¬a] = ¬¬a ¬a
        where
            ¬a∧¬¬a = negacion-disjuncion-implica-conjuncion-de-negaciones ¬[a∨¬a]
            ¬¬a = π₂ ¬a∧¬¬a
            ¬a = π₁ ¬a∧¬¬a

    implicacion-implica-neg-conjuncion : (A → B) → ¬ (A ∧ ¬ B)
    implicacion-implica-neg-conjuncion [a→b] [a∧¬b] = ¬b b
        where
            a = π₁ [a∧¬b]
            b = [a→b] a
            ¬b = π₂ [a∧¬b]

    -- neg-conjuncion-implica-disjuncion : ¬ (A ∧ B) → (¬ A) ∨ (¬ B)     -- no se puede, requiere LEM
    -- neg-conjuncion-implica-disjuncion ¬[a∧b] = {!   !}

    

    --implicacion-implica-disjuncion : (A → B) → (¬ A) ∨ B
    --implicacion-implica-disjuncion a→b  = {! !}
        --where
            --¬[a∧¬b] = implicacion-implica-neg-conjuncion a→b

    --n-implicacion-implica-antecedente : ¬ (A → B) → A ∧ ¬ B
    --n-implicacion-implica-antecedente ¬[a→b] = {!   !}
    
    contradiccion : (A → ⊥) → (¬ A)
    contradiccion = λ h₁ → (λ h₂ → h₁ h₂)
    
    explosion : ⊥ → A
    explosion = λ ()

    disjuncion-implica-implicacion : (¬ A) ∨ B → (A → B)
    disjuncion-implica-implicacion (inl ¬a) a = explosion (¬a a)
    disjuncion-implica-implicacion (inr b) a = b

    neg-top-implica-bot : ¬ ⊤ → ⊥
    neg-top-implica-bot x = x ⋆     --- Como siempre ⊤, entonces puedo usar ⊤ para evaluar en ¬ ⊤

    neg-bot-implica-top : ¬ ⊥ → ⊤
    neg-bot-implica-top ¬⊥ = ⋆
    
    dnn-top : (¬ ¬ ⊤) → ⊤
    dnn-top ¬¬⊤ = ⋆

    exer-743 : ¬ (A ∨ B) → ¬ A
    exer-743 ¬[a∨b] a = ¬[a∨b] (inl a)

    propo : A → ( ( ⊤ ∨ A ) → ⊤ )
    propo = λ a → λ ⋆∨a → ⋆
    

    {- φ(x) = (x < 0)
    ∀ x . φ - enunciado

    P(x) - si x es libre, y no hay otras variables libres, entonces P(x) 
    es un .

    Asociatividad siempre a la derecha
 -}
    -- Π(x:A) P(x) : Prop
    -- data ∀ₚ (A : 𝓤₀ ̇) {P : A → 𝓤₀ ̇} : 𝓤₀ ̇  where
    --     ∀ₚ-intro :(x : A) → P → ∀ₚ A P
    -- 
    -- ∀-elim : {P : 𝓤₀ ̇  → 𝓤₀ ̇} → (∀ (x : 𝓤₀ ̇ ) → (P x)) → (s : 𝓤₀ ̇ ) → P s
    -- ∀-elim = λ z → z
-- 
    -- exampl-725 : {B : 𝓤₀ ̇  → 𝓤₀ ̇} → (∀ (x : 𝓤₀ ̇ ) → (A ∧ B x))
    --             ---------------------------------------------
    --             → (A ∧ (∀ (x : 𝓤₀ ̇ ) → (B x)))
    -- exampl-725 {B} h₁ = ⟨ π₁ (h₁ B) , (λ (x) → π₂ (h₁ x)) ⟩