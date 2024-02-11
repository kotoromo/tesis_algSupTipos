open import Notacion
open import Igualdad
open import Agda.Primitive

module Funciones where

    -- Por definición, una función f : A → B es un objeto que manda un termino a : A
    -- en un único termino de tipo (f a) : B

    _es-funcion_ : ∀ {A B : Type} (f : A → B) {a a' : A}
                → a ≡ a'
                ------------------
                → (f a) ≡ (f a')

    f es-funcion (refl a) = refl (f a)

    _∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level}
            {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
            → (B → C)
            → (A → B)
            --------------------------
            → (A → C)
    
    f ∘ g = λ x → f (g x)

    infixl 10 _∘_
    

    -- https://unimath.github.io/agda-unimath/foundation-core.injective-maps.html

    _es-inyectiva : ∀ {A B : Type} (f : A → B)
                    -------------------------------------
                    → Type
    
    _es-inyectiva {A} {B} f = ∀ {x y : A} → ((f x) ≡ (f y)) → (x ≡ y)


    _es-mono : ∀ {A B C : Type} 
                 (f : A → B)
               → Type  
    
    _es-mono {A} {B} {C} f = ∀ (g h : C → A) → 
                ((f ∘ g ≡ f ∘ h) → g ≡ h)