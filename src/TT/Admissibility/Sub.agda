
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

module TT.Admissibility.Sub where

sub-typ-eqv : {d : Dim} {Γ : Ctx} {A B : Typ Γ d}               {σ : Sub Γ} (A≡B : Γ ⊢ A ≡ B)     (⊢σ∷ : Γ ⊢ σ ∷sub) → Γ [ σ ] ⊢ A [ σ ] ≡ B [ σ ]
sub-trm-eqv : {d : Dim} {Γ : Ctx} {t u : Trm Γ d} {A : Typ Γ d} {σ : Sub Γ} (t≡u : Γ ⊢ t ≡ u ∷ A) (⊢σ∷ : Γ ⊢ σ ∷sub) → Γ [ σ ] ⊢ t [ σ ] ≡ u [ σ ] ∷ A [ σ ]

instance
  denote-sub-typ-eqv : {d : Dim} {Γ : Ctx} {A B : Typ Γ d}               {σ : Sub Γ} → OpNotation (Γ ⊢ A ≡ B)     (λ _ → Γ ⊢ σ ∷sub) (λ _ _ → Γ [ σ ] ⊢ A [ σ ] ≡ B [ σ ])
  _[_] ⦃ denote-sub-typ-eqv ⦄ = sub-typ-eqv
  denote-sub-trm-eqv : {d : Dim} {Γ : Ctx} {t u : Trm Γ d} {A : Typ Γ d} {σ : Sub Γ} → OpNotation (Γ ⊢ t ≡ u ∷ A) (λ _ → Γ ⊢ σ ∷sub) (λ _ _ → Γ [ σ ] ⊢ t [ σ ] ≡ u [ σ ] ∷ A [ σ ])
  _[_] ⦃ denote-sub-trm-eqv ⦄ = sub-trm-eqv

sub-ctx-typing :           {Γ : Ctx} {σ : Sub Γ} → Γ ⊢ → Γ ⊢ σ ∷sub → Γ [ σ ] ⊢
sub-typ-typing : {d : Dim} {Γ : Ctx} {A : Typ Γ d} {σ : Sub Γ} → Γ ⊢ A → Γ ⊢ σ ∷sub → Γ [ σ ] ⊢ A [ σ ]
sub-trm-typing : {d : Dim} {Γ : Ctx} {A : Typ Γ d} {t : Trm Γ d} {σ : Sub Γ} → Γ ⊢ t ∷ A → Γ ⊢ σ ∷sub → Γ [ σ ] ⊢ t [ σ ] ∷ A [ σ ]

instance
  denote-sub-ctx-typing : {Γ : Ctx} {σ : Sub Γ} → OpNotation (Γ ⊢) (λ _ → Γ ⊢ σ ∷sub) (λ _ _ → Γ [ σ ] ⊢)
  _[_] ⦃ denote-sub-ctx-typing ⦄ = sub-ctx-typing
  denote-sub-typ-typing : {d : Dim} {Γ : Ctx} {A : Typ Γ d} {σ : Sub Γ} → OpNotation (Γ ⊢ A) (λ _ → Γ ⊢ σ ∷sub) (λ _ _ → Γ [ σ ] ⊢ A [ σ ])
  _[_] ⦃ denote-sub-typ-typing ⦄ = sub-typ-typing
  denote-sub-trm-typing : {d : Dim} {Γ : Ctx} {A : Typ Γ d} {t : Trm Γ d} {σ : Sub Γ} → OpNotation (Γ ⊢ t ∷ A) (λ _ → Γ ⊢ σ ∷sub) (λ _ _ → Γ [ σ ] ⊢ t [ σ ] ∷ A [ σ ])
  _[_] ⦃ denote-sub-trm-typing ⦄ = sub-trm-typing

sub-typ-eqv (refl Γ⊢ ⊢A)                ⊢σ∷ = refl (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ])
sub-typ-eqv (trans Γ⊢ ⊢A ⊢B ⊢C A≡B B≡C) ⊢σ∷ = trans (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (⊢C [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (B≡C [ ⊢σ∷ ])
sub-typ-eqv (symm Γ⊢ ⊢A ⊢B A≡B)         ⊢σ∷ = symm (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ])

sub-typ-eqv {σ = σ} (Π₁ {d₀} {d₁} {Γ} Γ⊢ {A} {B} ⊢A ⊢B A≡B {F} ⊢F) ⊢σ∷
  = cast-typ-eqv
      refl
      (≅-symm (≅-typ-Π refl refl (rew-sub-typ F σ A B 𝟙)))
      (Π₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷sub
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
sub-typ-eqv {σ = σ} (Π₂ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A ⊢F ⊢G F≡G) ⊢σ∷
  = Π₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (⊢G [ ⊢σ↑∷ ]) (F≡G [ ⊢σ↑∷ ])
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷sub
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
sub-typ-eqv {σ = σ} (E Γ⊢ t∷ u∷ t≡u) ⊢σ∷ = E (Γ⊢ [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ]) (t≡u [ ⊢σ∷ ])

sub-typ-eqv {σ = σ} (≃₁ Γ⊢ ⊢A ⊢B A≡B t∷ u∷)     ⊢σ∷ = ≃₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ])
sub-typ-eqv {σ = σ} (≃₂ Γ⊢ ⊢A t₁∷ t₂∷ t₁≡t₂ u∷) ⊢σ∷ = ≃₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ∷ ]) (t₁≡t₂ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ])
sub-typ-eqv {σ = σ} (≃₃ Γ⊢ ⊢A t∷ u₁∷ u₂∷ u₁≡u₂) ⊢σ∷ = ≃₃ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u₁∷ [ ⊢σ∷ ]) (u₂∷ [ ⊢σ∷ ]) (u₁≡u₂ [ ⊢σ∷ ])

sub-trm-eqv {σ = σ} (β {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F {f} f∷ {B} ⊢B {t} t∷ A≡B) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (sub-sub-trm f σ A t 𝟙))
      (≅-symm (sub-sub-typ F σ A t 𝟙))
      (β (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ [,] Γ⊢ ⊢σ∷ ⊢A ]) (f∷ [ [,] Γ⊢ ⊢σ∷ ⊢A ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]))
sub-trm-eqv {σ = σ} (η {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F {f} f∷) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-ƛ refl refl refl (≅-trm-·
        refl
        (nxt-sub-typ A σ A 𝟙)
        (nxt-sub-typ F σ A (𝟙 , A))
        (nxt-sub-trm f σ A 𝟙)
        (nxt-sub-typ A σ A 𝟙)
        (≅-trm-` refl (nxt-sub-typ A σ A 𝟙) refl))))
      refl
      (η (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ [,] Γ⊢ ⊢σ∷ ⊢A ]) (f∷ [ ⊢σ∷ ]))

sub-trm-eqv {σ = σ} (irrel {Γ} Γ⊢ {A} ⊢A {t} t∷ {u} u∷) ⊢σ∷
  = irrel (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ])

sub-trm-eqv {σ = σ} (≃ind-β {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ))
      (≃ind-β (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷sub
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷sub
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎

sub-trm-eqv (refl Γ⊢ ⊢A t∷)                ⊢σ∷ = refl (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ])
sub-trm-eqv (trans Γ⊢ ⊢A s∷ t∷ u∷ A≡B B≡C) ⊢σ∷ = trans (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (s∷ [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (B≡C [ ⊢σ∷ ])
sub-trm-eqv (symm Γ⊢ ⊢A t∷ u∷ t≡u)         ⊢σ∷ = symm (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ]) (t≡u [ ⊢σ∷ ])

sub-trm-eqv (conv Γ⊢ ⊢A ⊢B t∷A u∷A t≡u A≡B) ⊢σ∷ = conv (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷A [ ⊢σ∷ ]) (u∷A [ ⊢σ∷ ]) (t≡u [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ])

sub-trm-eqv {σ = σ} (ƛ₁ {d₀} {d₁} {Γ} Γ⊢ {A} {B} ⊢A ⊢B A≡B {F} ⊢F {f} f∷) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-ƛ refl refl (rew-sub-typ F σ A B 𝟙) (rew-sub-trm f σ A B 𝟙)))
      refl
      (ƛ₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ↑∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷sub
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
sub-trm-eqv {σ = σ} (ƛ₂ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A ⊢F ⊢G F≡G f∷) ⊢σ∷
  = ƛ₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (⊢G [ ⊢σ↑∷ ]) (F≡G [ ⊢σ↑∷ ]) (f∷ [ ⊢σ↑∷ ])
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷sub
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
sub-trm-eqv {σ = σ} (ƛ₃ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A ⊢F f∷ g∷ f≡g) ⊢σ∷
  = ƛ₃ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ↑∷ ]) (g∷ [ ⊢σ↑∷ ]) (f≡g [ ⊢σ↑∷ ])
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷sub
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A

sub-trm-eqv {σ = σ} (·₁ {d₀} {d₁} {Γ} Γ⊢ {A} {C} ⊢A ⊢C A≡C {F} ⊢F f∷ ⊢B {t} t∷) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-· refl refl (rew-sub-typ F σ A C 𝟙) refl refl refl))
      (≅-symm (sub-sub-typ F σ _ t 𝟙))
      (·₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢C [ ⊢σ∷ ]) (A≡C [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷sub
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
sub-trm-eqv {σ = σ} (·₂ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F ⊢G F≡G f∷ ⊢B {t} t∷) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-sub-typ F σ _ t 𝟙))
      (·₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (⊢G [ ⊢σ↑∷ ]) (F≡G [ ⊢σ↑∷ ]) (f∷ [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷sub
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
sub-trm-eqv {σ = σ} (·₃ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F f∷ g∷ f≡g ⊢B {t} t∷) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-sub-typ F σ _ t 𝟙))
      (·₃ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ∷ ]) (g∷ [ ⊢σ∷ ]) (f≡g [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷sub
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
sub-trm-eqv {σ = σ} (·₄ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F f∷ ⊢B ⊢D B≡D {t} t∷) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-sub-typ F σ _ t 𝟙))
      (·₄ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (⊢D [ ⊢σ∷ ]) (B≡D [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷sub
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A
sub-trm-eqv {σ = σ} (·₅ {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F f∷ ⊢B {t} t∷ u∷ t≡u) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-sub-typ F σ _ t 𝟙))
      (·₅ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ ⊢σ↑∷ ]) (f∷ [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ]) (t≡u [ ⊢σ∷ ]))
  where ⊢σ↑∷ : Γ , A ⊢ σ , _ ∷sub
        ⊢σ↑∷ = [,] Γ⊢ ⊢σ∷ ⊢A

sub-trm-eqv (≃rfl₁ Γ⊢ ⊢A ⊢B A≡B t∷) ⊢σ∷ = ≃rfl₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ])
sub-trm-eqv (≃rfl₂ Γ⊢ ⊢A t∷ u∷ t≡u) ⊢σ∷ = ≃rfl₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ]) (t≡u [ ⊢σ∷ ])

sub-trm-eqv {σ = σ} (≃ind₁ {d} {Γ} Γ⊢ {A₁} {B₁} ⊢A₁ ⊢B₁ A₁≡B₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-≃ind refl refl (rew-sub-typ A₂ σ _ _ 𝟙) refl (rew-sub-trm t₂ σ _ _ 𝟙) (rew-sub-typ F σ _ _ (𝟙 , _)) refl refl refl))
      (≅-symm (sub-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₁ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢B₁ [ ⊢σ∷ ]) (A₁≡B₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷sub
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷sub
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
sub-trm-eqv {σ = σ} (≃ind₂ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} {B₂} ⊢A₂ ⊢B₂ A₂≡B₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-≃ind refl refl refl refl refl (rew-sub-typ F (σ , A₁) _ _ 𝟙) refl refl refl))
      (≅-symm (sub-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₂ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (⊢B₂ [ ⊢σ↑∷ ]) (A₂≡B₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷sub
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷sub
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
sub-trm-eqv {σ = σ} (≃ind₃ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} {τ₁} t₁∷ τ₁∷ t₁≡τ₁ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₃ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (τ₁∷ [ ⊢σ∷ ]) (t₁≡τ₁ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷sub
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷sub
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
sub-trm-eqv {σ = σ} (≃ind₄ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} {τ₂} t₂∷ τ₂∷ t₂≡τ₂ {F} ⊢F {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      (≅-symm (≅-trm-≃ind refl refl refl refl refl (rew-sub-typ F (σ , A₁) _ _ 𝟙) refl refl refl))
      (≅-symm (sub-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₄ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (τ₂∷ [ ⊢σ↑∷ ]) (t₂≡τ₂ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷sub
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷sub
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
sub-trm-eqv {σ = σ} (≃ind₅ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} {G} ⊢F ⊢G F≡G {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₅ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) (⊢G [ ⊢σ↑↑∷ ]) (F≡G [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷sub
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷sub
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
sub-trm-eqv {σ = σ} (≃ind₆ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} {g} f∷ g∷ f≡g {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₆ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ g[σ]∷ f[σ]≡g[σ] (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷sub
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷sub
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        g[σ]∷ : Γ [ σ ] ⊢ g [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        g[σ]∷ = cast-trm-typing
                  refl
                  (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (g∷ [ ⊢σ∷ ])
        f[σ]≡g[σ] : Γ [ σ ] ⊢ f [ σ ] ≡ g [ σ ]
                            ∷ F [ σ , _ , _ ]
                                [ sub (t₁ [ σ ]) , _ ]
                                [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]≡g[σ] = cast-trm-eqv
                      refl
                      refl
                      (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                      (f≡g [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
sub-trm-eqv {σ = σ} (≃ind₇ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} {ω} u∷ ω∷ u≡ω {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₇ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (ω∷ [ ⊢σ∷ ]) (u≡ω [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷sub
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷sub
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
sub-trm-eqv {σ = σ} (≃ind₈ {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} u∷ {p} {ρ} p∷ ρ∷ p≡ρ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-eqv
      refl
      refl
      (≅-symm (sub-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      (≃ind₈ (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) (ρ∷ [ ⊢σ∷ ]) (p≡ρ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷sub
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷sub
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎

data Var⊕Trm-Typing {d : Dim} {Γ : Ctx} (A : Typ Γ d) : (x : Var Γ d ⊕ Trm Γ d) → Set where
  inl : {v : Var Γ d} → var-typ v ≅ A → Var⊕Trm-Typing A (inl v)
  inr : {t : Trm Γ d} → Γ ⊢ t ∷ A     → Var⊕Trm-Typing A (inr t)

wkn-var⊕trm-typing : {d : Dim} {Γ : Ctx} {A : Typ Γ d} {x : Var Γ d ⊕ Trm Γ d} {σ : Wkn Γ} (Γ⊢x∷A : Var⊕Trm-Typing A x) (Γ⊢σ∷wkn : Γ ⊢ σ ∷wkn) → Var⊕Trm-Typing (A [ σ ]) (x [ σ ])
wkn-var⊕trm-typing {d} {Γ} {A} {_} {σ} (inl {v} refl) Γ⊢σ∷wkn = inl (≅-symm (wkn-var-typ v σ))
wkn-var⊕trm-typing (inr Γ⊢t∷A)  Γ⊢σ∷wkn = inr (Γ⊢t∷A [ Γ⊢σ∷wkn ])

instance
  denote-wkn-var⊕trm-typing : {d : Dim} {Γ : Ctx} {A : Typ Γ d} {x : Var Γ d ⊕ Trm Γ d} {σ : Wkn Γ} → OpNotation (Var⊕Trm-Typing A x) (λ _ → Γ ⊢ σ ∷wkn) (λ _ _ → Var⊕Trm-Typing (A [ σ ]) (x [ σ ]))
  _[_] ⦃ denote-wkn-var⊕trm-typing ⦄ = wkn-var⊕trm-typing

var-typ-typing-sub : {d : Dim} {Γ : Ctx} (v : Var Γ d) (σ : Sub Γ) → Γ ⊢ → Γ ⊢ σ ∷sub → Γ [ σ ] ⊢ → Γ [ σ ] ⊢ var-typ v [ σ ]
var-typ-typing-sub z     (sub {Γ} {d} {A} t) ([,] Γ⊢ Γ⊢A) ([sub] _ _ Γ⊢t∷A) _
  rewrite ≡-of-≅ (wkn-sub-typ A A t 𝟙)
  = Γ⊢A
var-typ-typing-sub (s v) (sub {Γ} {d} {A} t) ([,] Γ⊢ Γ⊢A) ([sub] _ _ Γ⊢t∷A) _
  rewrite ≡-of-≅ (wkn-sub-typ (var-typ v) A t 𝟙)
  = var-typ-typing v Γ⊢
var-typ-typing-sub z     (_,_ {Γ} {d} σ A)   ([,] Γ⊢ Γ⊢A) ([,]   _ Γ⊢σ∷sub _) ([,] Γσ⊢ Γσ⊢Aσ)
  rewrite ≡-of-≅ (nxt-sub-typ A σ A 𝟙)
  = Γσ⊢Aσ [ [wkn] Γσ⊢ Γσ⊢Aσ ]
var-typ-typing-sub (s v) (_,_ {Γ} {d} σ A)   ([,] Γ⊢ Γ⊢A) ([,]   _ Γ⊢σ∷sub _) ([,] Γσ⊢ Γσ⊢Aσ)
  rewrite ≡-of-≅ (nxt-sub-typ (var-typ v) σ A 𝟙)
  = var-typ-typing-sub v σ Γ⊢ Γ⊢σ∷sub Γσ⊢ [ [wkn] Γσ⊢ Γσ⊢Aσ ]

sub-var-typing : {d : Dim} {Γ : Ctx} (v : Var Γ d) (σ : Sub Γ) → Γ ⊢ σ ∷sub → Γ [ σ ] ⊢ → Var⊕Trm-Typing (var-typ v [ σ ]) (v [ σ ])
sub-var-typing  z         (sub {Γ} {d} {A} t) ([sub] Γ⊢ Γ⊢A Γ⊢t∷A) _
  rewrite ≡-of-≅ (wkn-sub-typ A A t 𝟙)
  = inr Γ⊢t∷A
sub-var-typing  (s v)     (sub {Γ} {d} {A} t) ([sub] Γ⊢ Γ⊢A Γ⊢t∷A) _
  rewrite ≡-of-≅ (wkn-sub-typ (var-typ v) A t 𝟙)
  = inl refl
sub-var-typing  z         (_,_ {Γ} {d} σ A)   ([,]   Γ⊢ Γ⊢σ∷sub Γ⊢A) ([,] Γσ⊢ Γσ⊢Aσ)
  rewrite ≡-of-≅ (nxt-sub-typ A σ A 𝟙)
  = inl refl
sub-var-typing  (s {Γ} v) (σ , A)             ([,]   Γ⊢ Γ⊢σ∷sub Γ⊢A) ([,] Γσ⊢ Γσ⊢Aσ)
  rewrite ≡-of-≅ (nxt-sub-typ (var-typ v) σ A 𝟙)
  = sub-var-typing v σ Γ⊢σ∷sub Γσ⊢ [ [wkn] Γσ⊢ Γσ⊢Aσ ]

trm-of-var⊕trm-typing : {d : Dim} {Γ : Ctx} {A B : Typ Γ d} {x : Var Γ d ⊕ Trm Γ d} → Γ ⊢ → Γ ⊢ A → Γ ⊢ B → Var⊕Trm-Typing A x → Γ ⊢ A ≡ B → Γ ⊢ trm-of-var⊕trm B x ∷ B
trm-of-var⊕trm-typing Γ⊢ Γ⊢A Γ⊢B (inl refl) Γ⊢A≡B = [`] Γ⊢ Γ⊢B Γ⊢A≡B
trm-of-var⊕trm-typing Γ⊢ Γ⊢A Γ⊢B (inr Γ⊢t∷A)  Γ⊢A≡B = conv Γ⊢ Γ⊢A Γ⊢B Γ⊢A≡B Γ⊢t∷A

sub-ctx-typing ([,] Γ⊢ ⊢A) ([sub] _ _ t∷)  = Γ⊢
sub-ctx-typing ([,] Γ⊢ ⊢A) ([,]   _ ⊢σ∷ _) = [,] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ])

sub-typ-typing ([Π] Γ⊢ ⊢A ⊢F) ⊢σ∷ = [Π] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ [,] Γ⊢ ⊢σ∷ ⊢A ])
sub-typ-typing ([U] Γ⊢)       ⊢σ∷ = [U] (Γ⊢ [ ⊢σ∷ ])
sub-typ-typing ([E] Γ⊢ t∷)    ⊢σ∷ = [E] (Γ⊢ [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ])

sub-typ-typing ([≃] Γ⊢ ⊢A t∷ u∷) ⊢σ∷ = [≃] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (u∷ [ ⊢σ∷ ])

sub-trm-typing {σ = σ} (conv Γ⊢ ⊢A ⊢B t∷ A≡B) ⊢σ∷ = conv (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ])
sub-trm-typing {σ = σ} ([`] {d} {Γ} Γ⊢ {A} ⊢A {v} ⊢typv≡A) ⊢σ∷ = trm-of-var⊕trm-typing (Γ⊢ [ ⊢σ∷ ]) (var-typ-typing-sub v σ Γ⊢ ⊢σ∷ (Γ⊢ [ ⊢σ∷ ])) (⊢A [ ⊢σ∷ ]) (sub-var-typing v σ ⊢σ∷ (Γ⊢ [ ⊢σ∷ ])) (⊢typv≡A [ ⊢σ∷ ])
sub-trm-typing ([ƛ] Γ⊢ ⊢A ⊢F f∷) ⊢σ∷ = [ƛ] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ [,] Γ⊢ ⊢σ∷ ⊢A ]) (f∷ [ [,] Γ⊢ ⊢σ∷  ⊢A ])
sub-trm-typing {σ = σ} ([·] {d₀} {d₁} {Γ} Γ⊢ {A} ⊢A {F} ⊢F {f} f∷ {B} ⊢B {t} t∷ A≡B) ⊢σ∷
  rewrite ≡-of-≅ (sub-sub-typ F σ A t 𝟙)
  = [·] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (⊢F [ [,] Γ⊢ ⊢σ∷ ⊢A ] ) (f∷ [ ⊢σ∷ ]) (⊢B [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ]) (A≡B [ ⊢σ∷ ])

sub-trm-typing ([≃rfl] Γ⊢ ⊢A t∷) ⊢σ∷ = [≃rfl] (Γ⊢ [ ⊢σ∷ ]) (⊢A [ ⊢σ∷ ]) (t∷ [ ⊢σ∷ ])
sub-trm-typing {σ = σ} ([≃ind] {d} {Γ} Γ⊢ {A₁} ⊢A₁ {A₂} ⊢A₂ {t₁} t₁∷ {t₂} t₂∷ {F} ⊢F {f} f∷ {u} u∷ {p} p∷ A₁↑≅A₂ t₁↑≅t₂) ⊢σ∷
  = cast-trm-typing
      refl
      (≅-symm (sub-≃ind-F Γ A₁ A₂ u t₂ F p σ))
      ([≃ind] (Γ⊢ [ ⊢σ∷ ]) (⊢A₁ [ ⊢σ∷ ]) (⊢A₂ [ ⊢σ↑∷ ]) (t₁∷ [ ⊢σ∷ ]) (t₂∷ [ ⊢σ↑∷ ]) (⊢F [ ⊢σ↑↑∷ ]) f[σ]∷ (u∷ [ ⊢σ∷ ]) (p∷ [ ⊢σ∷ ]) A₁[σ]↑≅A₂[σ↑] t₁[σ]↑≅t₂[σ↑])
  where Γ↑⊢ : Γ , A₁ ⊢
        Γ↑⊢ = [,] Γ⊢ ⊢A₁
        A₁↑≡A₂ : Γ , A₁ ⊢ A₁ [ wkn A₁ ] ≡ A₂
        A₁↑≡A₂ = typ-≡-of-≅ Γ↑⊢ ⊢A₂ A₁↑≅A₂
        ⊢≃⋯∷ : Γ , A₁ ⊢ ≃ A₂ t₂ (` A₂ z)
        ⊢≃⋯∷ = [≃] Γ↑⊢ ⊢A₂ t₂∷ ([`] Γ↑⊢ ⊢A₂ A₁↑≡A₂)
        Γ↑↑⊢ : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢
        Γ↑↑⊢ = [,] Γ↑⊢ ⊢≃⋯∷
        ⊢σ↑∷   : Γ , A₁ ⊢ σ , _ ∷sub
        ⊢σ↑∷   = [,] Γ⊢ ⊢σ∷ ⊢A₁
        ⊢σ↑↑∷  : Γ , A₁ , ≃ A₂ t₂ (` A₂ z) ⊢ σ , _ , _ ∷sub
        ⊢σ↑↑∷  = [,] Γ↑⊢ ⊢σ↑∷ ⊢≃⋯∷
        f[σ]∷ : Γ [ σ ] ⊢ f [ σ ]
                         ∷ F [ σ , _ , _ ]
                             [ sub (t₁ [ σ ]) , _ ]
                             [ sub (≃rfl (A₁ [ σ ]) (t₁ [ σ ])) ]
        f[σ]∷ = cast-trm-typing
                  refl
                  (sub-≃ind-F Γ A₁ A₂ t₁ t₂ F (≃rfl A₁ t₁) σ)
                  (f∷ [ ⊢σ∷ ])
        A₁[σ]↑≅A₂[σ↑] : A₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ A₂ [ σ , A₁ ]
        A₁[σ]↑≅A₂[σ↑] =
          begin
            A₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-typ A₁ _ _ 𝟙) ⟩
            A₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-typ refl A₁↑≅A₂ refl ⟩
            A₂ [ σ , A₁ ]
          ∎
        t₁[σ]↑≅t₂[σ↑] : t₁ [ σ ] [ wkn (A₁ [ σ ]) ] ≅ t₂ [ σ , A₁ ]
        t₁[σ]↑≅t₂[σ↑] =
          begin
            t₁ [ σ ] [ wkn (A₁ [ σ ]) ]
          ≅⟨ ≅-symm (nxt-sub-trm t₁ _ _ 𝟙) ⟩
            t₁ [ wkn A₁ ] [ σ , A₁ ]
          ≅⟨ ≅-sub-trm refl t₁↑≅t₂ refl ⟩
            t₂ [ σ , A₁ ]
          ∎
