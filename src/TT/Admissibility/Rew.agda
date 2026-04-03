
open import OpsNotation
open import HEq
open import Either

open import TT.Syntax
open import TT.Typing
open import TT.HEq
open import TT.Telescope
open import TT.OpsLemmas
open import TT.HeqLemmas

open import TT.Admissibility.Wkn

module TT.Admissibility.Rew where

rew-typ-eqv : {d : Dim} {Γ : Ctx} {A B : Typ Γ d}               {σ : Rew Γ} (A≡B : Γ ⊢ A ≡ B)     (⊢σ∷ : Γ ⊢ σ ∷rew) → Γ [ σ ] ⊢ A [ σ ] ≡ B [ σ ]
rew-trm-eqv : {d : Dim} {Γ : Ctx} {t u : Trm Γ d} {A : Typ Γ d} {σ : Rew Γ} (t≡u : Γ ⊢ t ≡ u ∷ A) (⊢σ∷ : Γ ⊢ σ ∷rew) → Γ [ σ ] ⊢ t [ σ ] ≡ u [ σ ] ∷ A [ σ ]

instance
  denote-rew-typ-eqv : {d : Dim} {Γ : Ctx} {A B : Typ Γ d}               {σ : Rew Γ} → OpNotation (Γ ⊢ A ≡ B)     (λ _ → Γ ⊢ σ ∷rew) (λ _ _ → Γ [ σ ] ⊢ A [ σ ] ≡ B [ σ ])
  _[_] ⦃ denote-rew-typ-eqv ⦄ = rew-typ-eqv
  denote-rew-trm-eqv : {d : Dim} {Γ : Ctx} {t u : Trm Γ d} {A : Typ Γ d} {σ : Rew Γ} → OpNotation (Γ ⊢ t ≡ u ∷ A) (λ _ → Γ ⊢ σ ∷rew) (λ _ _ → Γ [ σ ] ⊢ t [ σ ] ≡ u [ σ ] ∷ A [ σ ])
  _[_] ⦃ denote-rew-trm-eqv ⦄ = rew-trm-eqv

rew-ctx-typing :           {Γ : Ctx} {σ : Rew Γ} → Γ ⊢ → Γ ⊢ σ ∷rew → Γ [ σ ] ⊢
rew-typ-typing : {d : Dim} {Γ : Ctx} {A : Typ Γ d} {σ : Rew Γ} → Γ ⊢ A → Γ ⊢ σ ∷rew → Γ [ σ ] ⊢ A [ σ ]
rew-trm-typing : {d : Dim} {Γ : Ctx} {A : Typ Γ d} {t : Trm Γ d} {σ : Rew Γ} → Γ ⊢ t ∷ A → Γ ⊢ σ ∷rew → Γ [ σ ] ⊢ t [ σ ] ∷ A [ σ ]

instance
  denote-rew-ctx-typing : {Γ : Ctx} {σ : Rew Γ} → OpNotation (Γ ⊢) (λ _ → Γ ⊢ σ ∷rew) (λ _ _ → Γ [ σ ] ⊢)
  _[_] ⦃ denote-rew-ctx-typing ⦄ = rew-ctx-typing
  denote-rew-typ-typing : {d : Dim} {Γ : Ctx} {A : Typ Γ d} {σ : Rew Γ} → OpNotation (Γ ⊢ A) (λ _ → Γ ⊢ σ ∷rew) (λ _ _ → Γ [ σ ] ⊢ A [ σ ])
  _[_] ⦃ denote-rew-typ-typing ⦄ = rew-typ-typing
  denote-rew-trm-typing : {d : Dim} {Γ : Ctx} {A : Typ Γ d} {t : Trm Γ d} {σ : Rew Γ} → OpNotation (Γ ⊢ t ∷ A) (λ _ → Γ ⊢ σ ∷rew) (λ _ _ → Γ [ σ ] ⊢ t [ σ ] ∷ A [ σ ])
  _[_] ⦃ denote-rew-trm-typing ⦄ = rew-trm-typing

rew-typ-eqv (refl Γ⊢ ⊢A)                ⊢σ∷ = refl (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ])
rew-typ-eqv (trans Γ⊢ ⊢A ⊢B ⊢C A≡B B≡C) ⊢σ∷ = trans (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (⊢C [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (B≡C [ ⊢σ∷ ])
rew-typ-eqv (symm Γ⊢ ⊢A ⊢B A≡B)         ⊢σ∷ = symm (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ])

rew-typ-eqv {σ = σ} (Π₁ {d₀} {d₁} {Γ} Γ⊢ {A} {B} ⊢A ⊢B A≡B {F} ⊢F) ⊢σ∷
  = cast-typ-eqv
      refl
      (≅-symm (≅-typ-Π refl refl (rew-rew-typ F σ A B 𝟙)))
      (Π₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷rew
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
rew-typ-eqv {σ = σ} (Π₂ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A ⊢F ⊢G F≡G) ⊢σ∷
  = Π₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (⊢G [ ⊢σ↑∷ ]) (F≡G [ ⊢σ↑∷ ])
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷rew
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
rew-typ-eqv {σ = σ} (E Γ⊢ t∷ u∷ t≡u) ⊢σ∷ = E (Γ⊢ [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ]) (t≡u [ ⊢σ∷ ])

rew-typ-eqv {σ = σ} (≃₁ Γ⊢ ⊢A ⊢B A≡B t∷ u∷)     ⊢σ∷ = ≃₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ])
rew-typ-eqv {σ = σ} (≃₂ Γ⊢ ⊢A t₁∷ t₂∷ t₁≡t₂ u∷) ⊢σ∷ = ≃₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ∷ ]) (t₁≡t₂ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ])
rew-typ-eqv {σ = σ} (≃₃ Γ⊢ ⊢A t∷ u₁∷ u₂∷ u₁≡u₂) ⊢σ∷ = ≃₃ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u₁∷ [ ⊢σ∷ ]) (u₂∷ [ ⊢σ∷ ]) (u₁≡u₂ [ ⊢σ∷ ])

rew-trm-eqv {σ = σ} (β {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F {f} f∷ {B} ⊢B {t} t∷ A≡B) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (sub-rew-trm f σ A t 𝟙))
      (≅-symm (sub-rew-typ F σ A t 𝟙))
      (β (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ [,] Γ⊢ ⊢σ∷ ⊢A ]) (f∷ [ [,] Γ⊢ ⊢σ∷ ⊢A ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]))
rew-trm-eqv {σ = σ} (η {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F {f} f∷) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-ƛ refl refl refl (≅-trm-·
        refl
        (nxt-rew-typ A σ A 𝟙)
        (nxt-rew-typ F σ A (𝟙 , A))
        (nxt-rew-trm f σ A 𝟙)
        (nxt-rew-typ A σ A 𝟙)
        (≅-trm-` refl (nxt-rew-typ A σ A 𝟙) refl))))
      refl
      (η (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ [,] Γ⊢ ⊢σ∷ ⊢A ]) (f∷ [ ⊢σ∷ ]))

rew-trm-eqv {σ = σ} (irrel {Γ} Γ⊢ {A} ⊢A {t} t∷ {u} u∷) ⊢σ∷
  = irrel (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ])

rew-trm-eqv {σ = σ} (≃ind-β {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ))
      (≃ind-β (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷rew
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷rew
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎

rew-trm-eqv (refl Γ⊢ ⊢A t∷)                ⊢σ∷ = refl (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ])
rew-trm-eqv (trans Γ⊢ ⊢A s∷ t∷ u∷ A≡B B≡C) ⊢σ∷ = trans (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (s∷ [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (B≡C [ ⊢σ∷ ])
rew-trm-eqv (symm Γ⊢ ⊢A t∷ u∷ t≡u)         ⊢σ∷ = symm (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ]) (t≡u [ ⊢σ∷ ])

rew-trm-eqv (conv Γ⊢ ⊢A ⊢B t∷A u∷A t≡u A≡B) ⊢σ∷ = conv (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷A [ ⊢σ∷ ]) (u∷A [ ⊢σ∷ ]) (t≡u [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ])

rew-trm-eqv {σ = σ} (ƛ₁ {d₀} {d₁} {Γ} Γ⊢ {A} {B} ⊢A ⊢B A≡B {F} ⊢F {f} f∷) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-ƛ refl refl (rew-rew-typ F σ A B 𝟙) (rew-rew-trm f σ A B 𝟙)))
      refl
      (ƛ₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ↑∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷rew
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
rew-trm-eqv {σ = σ} (ƛ₂ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A ⊢F ⊢G F≡G f∷) ⊢σ∷
  = ƛ₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (⊢G [ ⊢σ↑∷ ]) (F≡G [ ⊢σ↑∷ ]) (f∷ [ ⊢σ↑∷ ])
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷rew
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
rew-trm-eqv {σ = σ} (ƛ₃ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A ⊢F f∷ g∷ f≡g) ⊢σ∷
  = ƛ₃ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ↑∷ ]) (g∷ [ ⊢σ↑∷ ]) (f≡g [ ⊢σ↑∷ ])
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷rew
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A

rew-trm-eqv {σ = σ} (·₁ {d₀} {d₁} {Γ} Γ⊢ {A} {C} ⊢A ⊢C A≡C {F} ⊢F f∷ ⊢B {t} t∷) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-· refl refl (rew-rew-typ F σ A C 𝟙) refl refl refl))
      (≅-symm (sub-rew-typ F σ _ t 𝟙))
      (·₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢C [ ⊢σ∷ ]) (A≡C [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷rew
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
rew-trm-eqv {σ = σ} (·₂ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F ⊢G F≡G f∷ ⊢B {t} t∷) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-rew-typ F σ _ t 𝟙))
      (·₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (⊢G [ ⊢σ↑∷ ]) (F≡G [ ⊢σ↑∷ ]) (f∷ [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷rew
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
rew-trm-eqv {σ = σ} (·₃ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F f∷ g∷ f≡g ⊢B {t} t∷) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-rew-typ F σ _ t 𝟙))
      (·₃ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ∷ ]) (g∷ [ ⊢σ∷ ]) (f≡g [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷rew
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
rew-trm-eqv {σ = σ} (·₄ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F f∷ ⊢B ⊢D B≡D {t} t∷) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-rew-typ F σ _ t 𝟙))
      (·₄ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (⊢D [ ⊢σ∷ ]) (B≡D [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷rew
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
rew-trm-eqv {σ = σ} (·₅ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F f∷ ⊢B {t} t∷ u∷ t≡u) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-rew-typ F σ _ t 𝟙))
      (·₅ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ]) (t≡u [ ⊢σ∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷rew
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A

rew-trm-eqv (≃rfl₁ Γ⊢ ⊢A ⊢B A≡B t∷) ⊢σ∷ = ≃rfl₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ])
rew-trm-eqv (≃rfl₂ Γ⊢ ⊢A t∷ u∷ t≡u) ⊢σ∷ = ≃rfl₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ]) (t≡u [ ⊢σ∷ ])

rew-trm-eqv {σ = σ} (≃ind₁ {d} {Γ} Γ⊢ {A₁} {B₁} ⊢A₁ ⊢B₁ A₁≡B₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-≃ind refl refl (rew-rew-typ A₂ σ _ _ 𝟙) refl (rew-rew-trm t₂ σ _ _ 𝟙) (rew-rew-typ F σ _ _ (𝟙 , _)) refl refl refl))
      (≅-symm (rew-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢B₁ [ ⊢σ∷ ]) (A₁≡B₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷rew
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷rew
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
rew-trm-eqv {σ = σ} (≃ind₂ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} {B₂} ⊢A₂ ⊢B₂ A₂≡B₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-≃ind refl refl refl refl refl (rew-rew-typ F (σ , A₁) _ _ 𝟙) refl refl refl))
      (≅-symm (rew-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (⊢B₂ [ ⊢σ↑∷ ]) (A₂≡B₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷rew
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷rew
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
rew-trm-eqv {σ = σ} (≃ind₃ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} {τ₁} t₁∷ τ₁∷ t₁≡τ₁ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (rew-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₃ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (τ₁∷ [ ⊢σ∷ ]) (t₁≡τ₁ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷rew
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷rew
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
rew-trm-eqv {σ = σ} (≃ind₄ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} {τ₂} t₂∷ τ₂∷ t₂≡τ₂ {F} ⊢F {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-≃ind refl refl refl refl refl (rew-rew-typ F (σ , A₁) _ _ 𝟙) refl refl refl))
      (≅-symm (rew-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₄ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (τ₂∷ [ ⊢σ↑∷ ]) (t₂≡τ₂ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷rew
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷rew
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
rew-trm-eqv {σ = σ} (≃ind₅ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} {G} ⊢F ⊢G F≡G {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (rew-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₅ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) (⊢G [ ⊢σ↑↑∷ ]) (F≡G [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷rew
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷rew
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
rew-trm-eqv {σ = σ} (≃ind₆ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} {g} f∷ g∷ f≡g {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (rew-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₆ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ g[σ]∷ f[σ]≡g[σ] (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷rew
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷rew
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        g[σ]∷ : Γ [ σ ] ⊢ g [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        g[σ]∷ = cast-trm-typing
                  refl
                  (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (g∷ [ ⊢σ∷ ])
        f[σ]≡g[σ] : Γ [ σ ] ⊢ f [ σ ] ≡ g [ σ ]
                            ∷ F [ σ , _ , _ ]
                                [ sub (t₁ [ σ ]) , _ ]
                                [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]≡g[σ] = cast-trm-eqv
                      refl
                      refl
                      (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                      (f≡g [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
rew-trm-eqv {σ = σ} (≃ind₇ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} {ω} u∷ ω∷ u≡ω {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (rew-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₇ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (ω∷ [ ⊢σ∷ ]) (u≡ω [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷rew
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷rew
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
rew-trm-eqv {σ = σ} (≃ind₈ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} u∷ {p} {ρ} p∷ ρ∷ p≡ρ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (rew-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₈ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) (ρ∷ [ ⊢σ∷ ]) (p≡ρ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷rew
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷rew
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎

var-rew-typ-typing : {d : Dim} {Γ : Ctx} (v : Var Γ d) (σ : Rew Γ) → Γ ⊢ σ ∷rew → Γ [ σ ] ⊢ → Γ [ σ ] ⊢ var-typ (v [ σ ])
var-rew-typ-typing z     (rew {Γ} A B) ([rew] Γ⊢ ⊢A ⊢B _) _
  = ⊢B [ [wkn] Γ⊢ ⊢B ]
var-rew-typ-typing (s v) (rew {Γ} A B) ([rew] Γ⊢ _ ⊢B _) _
  = var-typ-typing v Γ⊢ [ [wkn] Γ⊢ ⊢B ]
var-rew-typ-typing z     (_,_ {Γ} σ A) ([,] _ Γ⊢σ∷rew _) ([,] Γσ⊢ Γσ⊢Aσ)
  = Γσ⊢Aσ [ [wkn] Γσ⊢ Γσ⊢Aσ ]
var-rew-typ-typing (s v) (_,_ {Γ} σ A) ([,] Γ⊢ Γ⊢σ∷rew _) ([,] Γσ⊢ Γσ⊢Aσ)
  = var-rew-typ-typing v σ Γ⊢σ∷rew Γσ⊢ [ [wkn] Γσ⊢ Γσ⊢Aσ ]

var-typ-typing-rew : {d : Dim} {Γ : Ctx} (v : Var Γ d) (σ : Rew Γ) → Γ ⊢ σ ∷rew → Γ [ σ ] ⊢ → Γ [ σ ] ⊢ var-typ v [ σ ]
var-typ-typing-rew z     (rew {Γ} A B) ([rew] Γ⊢ ⊢A ⊢B _) _
  rewrite ≡-of-≅ (wkn-rew-typ A A B 𝟙)
  = ⊢A [ [wkn] Γ⊢ ⊢B ]
var-typ-typing-rew (s v) (rew {Γ} A B) ([rew] Γ⊢ _ ⊢B _) _
  rewrite ≡-of-≅ (wkn-rew-typ (var-typ v) A B 𝟙)
  = var-typ-typing v Γ⊢ [ [wkn] Γ⊢ ⊢B ]
var-typ-typing-rew z     (_,_ {Γ} σ A) ([,] _ Γ⊢σ∷rew _) ([,] Γσ⊢ Γσ⊢Aσ)
  rewrite ≡-of-≅ (nxt-rew-typ A σ A 𝟙)
  = Γσ⊢Aσ [ [wkn] Γσ⊢ Γσ⊢Aσ ]
var-typ-typing-rew (s v) (_,_ {Γ} σ A) ([,] Γ⊢ Γ⊢σ∷rew _) ([,] Γσ⊢ Γσ⊢Aσ)
  rewrite ≡-of-≅ (nxt-rew-typ (var-typ v) σ A 𝟙)
  = var-typ-typing-rew v σ Γ⊢σ∷rew Γσ⊢ [ [wkn] Γσ⊢ Γσ⊢Aσ ]

rew-var-typ : {d : Dim} {Γ : Ctx} (v : Var Γ d) (σ : Rew Γ) → (Γ⊢σ∷rew : Γ ⊢ σ ∷rew) → Γ [ σ ] ⊢
            → (          var-typ (v [ σ ]) ≅ var-typ v [ σ ])
            ⊕ (Γ [ σ ] ⊢ var-typ (v [ σ ]) ≡ var-typ v [ σ ])
rew-var-typ z     (rew A B) ([rew] Γ⊢ Γ⊢A Γ⊢B B≡A) _
  rewrite ≡-of-≅ (wkn-rew-typ A A B 𝟙)
  = inr (B≡A [ [wkn] Γ⊢ Γ⊢B ])
rew-var-typ (s v) (rew A B) ([rew] Γ⊢ Γ⊢A Γ⊢B A≡B) _
  rewrite ≡-of-≅ (wkn-rew-typ (var-typ v) A B 𝟙)
  = inl refl
rew-var-typ z     (σ , A) ([,] Γ⊢ Γ⊢σ∷rew Γ⊢A) _
  rewrite ≡-of-≅ (nxt-rew-typ A σ A 𝟙)
  = inl refl
rew-var-typ (s v) (σ , A) ([,] Γ⊢ Γ⊢σ∷rew Γ⊢A) ([,] Γ[σ]⊢ ⊢A[σ])
  rewrite ≡-of-≅ (nxt-rew-typ (var-typ v) σ A 𝟙)
  with rew-var-typ v σ Γ⊢σ∷rew Γ[σ]⊢
...  | inl typv≅A = inl (≅-wkn-typ refl typv≅A refl)
...  | inr typv≡A = inr (typv≡A [ [wkn] Γ[σ]⊢ ⊢A[σ] ])

rew-ctx-typing ([,] Γ⊢ ⊢A) ([rew] _ _ Γ⊢B _) = [,] Γ⊢ Γ⊢B
rew-ctx-typing ([,] Γ⊢ ⊢A) ([,]   _ ⊢σ∷ _)   = [,] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ])

rew-typ-typing ([Π] Γ⊢ ⊢A ⊢F) ⊢σ∷ = [Π] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ [,] Γ⊢ ⊢σ∷ ⊢A ])
rew-typ-typing ([U] Γ⊢)       ⊢σ∷ = [U] (Γ⊢ [ ⊢σ∷ ])
rew-typ-typing ([E] Γ⊢ t∷)    ⊢σ∷ = [E] (Γ⊢ [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ])

rew-typ-typing ([≃] Γ⊢ ⊢A t∷ u∷) ⊢σ∷ = [≃] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ])

rew-trm-typing {σ = σ} (conv Γ⊢ ⊢A ⊢B t∷ A≡B) ⊢σ∷ = conv (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ])
rew-trm-typing {σ = σ} ([`] {d} {Γ} Γ⊢ {A} ⊢A {v} ⊢typv≡A) ⊢σ∷
  with rew-var-typ v σ ⊢σ∷ (Γ⊢ [ ⊢σ∷ ])
... | inl typv≅A  = [`] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) p
                 where p : Γ [ σ ] ⊢ var-typ (v [ σ ]) ≡ A [ σ ]
                       p rewrite ≡-of-≅ typv≅A = ⊢typv≡A [ ⊢σ∷ ]
... | inr typv≡A = [`] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ])
                       (trans (Γ⊢ [ ⊢σ∷ ]) (var-rew-typ-typing v σ ⊢σ∷ (Γ⊢ [ ⊢σ∷ ])) (var-typ-typing-rew v σ ⊢σ∷ (Γ⊢ [ ⊢σ∷ ])) (⊢A [ ⊢σ∷ ]) typv≡A (⊢typv≡A [ ⊢σ∷ ]))
rew-trm-typing ([ƛ] Γ⊢ ⊢A ⊢F f∷) ⊢σ∷ = [ƛ] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ [,] Γ⊢ ⊢σ∷ ⊢A ]) (f∷ [ [,] Γ⊢ ⊢σ∷  ⊢A ])
rew-trm-typing {σ = σ} ([·] {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F {f} f∷ {B} ⊢B {t} t∷ A≡B) ⊢σ∷
  rewrite ≡-of-≅ (sub-rew-typ F σ A t 𝟙)
  = [·] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ [,] Γ⊢ ⊢σ∷ ⊢A ] ) (f∷ [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ])

rew-trm-typing ([≃rfl] Γ⊢ ⊢A t∷) ⊢σ∷ = [≃rfl] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ])
rew-trm-typing {σ = σ} ([≃ind] {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-typing
      refl
      (≅-symm (rew-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      ([≃ind] (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷rew
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷rew
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (rew-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-rew-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-rew-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
