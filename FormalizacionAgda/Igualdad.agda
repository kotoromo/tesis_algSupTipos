open import Notacion

module Igualdad where
    
    data _≡_ {T : Type} : T → T → Type where
        refl : (x : T) → x ≡ x 

    infixl 0 _≡_
    
    refl-≡ : ∀ {T : Type}
            → ∀ {x : T}
            ------------
            → x ≡ x
    refl-≡ {T} {x} = refl x

    sym-≡ : ∀ {T : Type}
            → ∀ {x y : T}
            → x ≡ y
            ---------------
            → y ≡ x
    
    sym-≡ {T} {x} {y} (refl y) = refl x

    trans-≡ : ∀ {T : Type}
            → ∀ {x y z : T}
            → x ≡ y
            → y ≡ z
            -----------------
            → x ≡ z

    trans-≡ {T} {x} {y} {z} (refl x) (refl y) = refl z

    module Razonamiento-≡ {T : Type} where

        infix 1 inicio_
        infix 2 _≡⟨⟩_ _≡⟨_⟩_
        infix 3 _■

        -- Marca el inicio de un razonamiento de igualdades

        inicio_ : ∀ {x y : T}
                → x ≡ y
                --------------
                → x ≡ y
    
        inicio x≡y = x≡y

        -- Razonamiento directo de igualdades

        _≡⟨⟩_ : ∀ (x : T) {y : T}
                → x ≡ y
                -------------
                → x ≡ y
        
        x ≡⟨⟩ x≡y = x≡y

        -- Razonamiento con igualdad de por medio

        _≡⟨_⟩_ : ∀ (x : T) {y z : T}
                → x ≡ y
                → y ≡ z
                ------------------
                → x ≡ z
        
        x ≡⟨ x≡y ⟩ y≡z = trans-≡ x≡y y≡z

        -- Indicar que nuestra cadena de igualdades termina

        _■ : ∀ (x : T)
            -----------
            → x ≡ x
        
        _■ x = refl x 
    
    open Razonamiento-≡
