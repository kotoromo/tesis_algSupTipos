open import Notacion
open import Igualdad
open import Funciones
open import Logica

module Naturales where

    data ℕ : Type where
        cero : ℕ
        σ    : ℕ → ℕ

    ℕ-equiv : ∀ {n m : ℕ} 
            → n ≡ m 
            ---------------
            → σ n ≡ σ m
    ℕ-equiv {n} {m} n≡m = σ es-funcion n≡m

    succ-es-inyectiva : σ es-inyectiva
    succ-es-inyectiva (refl (σ x)) = refl x

    succ-n≠cero : ∀ {n : ℕ}
                --------------
                → ¬ ((σ n) ≡ cero)
    
    succ-n≠cero ()

    ℕ-elim : ∀ {φ : ℕ → Type}
            → φ cero
            → (∀ {k : ℕ} → φ k → φ (σ k))
            ----------------------------
            → ∀ {n : ℕ} → φ n 
    
    ℕ-elim {φ} φ₀ φk⊃φσk {cero} = φ₀
    ℕ-elim {φ} φ₀ φk⊃φσk {σ n} = φk⊃φσk HI where
        HI : φ n
        HI = ℕ-elim {φ} φ₀ φk⊃φσk {n}
    
    module Orden-ℕ where

        _≤_ : ℕ → ℕ → Type
        m ≤ cero = 𝟘
        cero ≤ σ n = 𝟙
        σ m ≤ σ n = m ≤ n

        

    module Aritmetica-ℕ where
        --{          Suma            }--
        _+_ : ℕ → ℕ → ℕ
        m + cero = m
        m + σ n = σ (m + n)

        +-asocia : ∀{n m k : ℕ}
                -------------
                → ((n + m) + k) ≡ (n + (m + k))
        
        +-asocia = {!   !}
        
        +-conmuta : ∀{n m : ℕ}
                    -------------
                    → (n + m) ≡ (m + n)
        
        +-conmuta = {!   !}


        +-cancelable-izquierda : ∀{n m k : ℕ}
                                → (k + m) ≡ (k + n)
                                --------------
                                → m ≡ n
        
        +-cancelable-izquierda = {!   !}

        +-cancelable-derecha : ∀{n m k : ℕ}
                              → (m + k) ≡ (n + k)
                              --------------------
                              → m ≡ n
        
        +-cancelable-derecha = {!   !}

        --{          Producto        }--
        _·_ : ℕ → ℕ → ℕ
        m · cero = cero
        m · σ n = (m · n) + n


    open Aritmetica-ℕ
        