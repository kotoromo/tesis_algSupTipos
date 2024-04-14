{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

-- without-K deshabilita el axioma de Streicher-K

-- exact-split hace que Agda solo acepte definiciones
-- con el simbolo de igualdad que se comportan comportan
-- igualdad de juicios.

-- safe deshabilita funciones de agda que pueden hacer
-- Agda inconsistente

module MLTT where

-- public permite que cualquiera que importe MLTT pueda importar Universos

open import Universos public

-- se dará por entendido a lo largo de este documento que 𝓤 𝓥 𝓦 y 𝓣 son universos
variable
 𝓤 𝓥 𝓦 𝓣 : Universe

--    module Coproducto where
data _+_ {𝓤 𝓥} (X : 𝓤  ̇) (Y : 𝓥  ̇) : 𝓤 ⊔ 𝓥  ̇ where
    inl : X → X + Y
    inr : Y → X + Y

infixr 3 _+_

ind₊ : ∀ {X : 𝓤  ̇} {Y : 𝓥  ̇} (C : X + Y → 𝓦 ̇)
        → (∀ (x : X) → C (inl x))
        → (∀ (y : Y) → C (inr y))
        --------------------------
        → ∀ (z : X + Y) → C z

ind₊ C f g (inl x) = f x
ind₊ C f g (inr y) = g y


data 𝟙 : 𝓤₀ ̇ where
    ⋆ : 𝟙

data 𝟘 : 𝓤₀  ̇ where


{-
    Teorema (Principio de inducción del tipo unitario):
    
    Sea P una familia de tipos indizada por 𝟙. 
    Si ⋆ : 𝟙 satisface P, entonces cualquier x : 𝟙 satisface P.

    Prueba:

    Como ⋆ : 𝟙 satisface P, entonces tenemos p : P ⋆
    Luego, sea x : P. Como 𝟙 solo tiene un constructor,
    ⋆, entonces x ≡ ⋆ : 𝟙. Por lo tanto, basta ver que P ⋆,
    pero por hipótesis p : P ⋆!

    Esto concluye la prueba.

-}



𝟙-ind : (P : 𝟙 → 𝓤  ̇) 
       → P ⋆
       ----------
       → (x : 𝟙) → (P x)

𝟙-ind P p ⋆ = p

record _×_ (A : 𝓤  ̇) (B : 𝓥  ̇) : 𝓤 ⊔ 𝓥  ̇ where
    constructor ⟨_,_⟩
    field
        proj₁ : A
        proj₂ : B
infixr 2 _×_

{-
    Dados dos tipos A y B, podemos obtener una funcion generica de A en B
    y evaluarla

-}

lemma : ∀ {A B : 𝓤} → A :  