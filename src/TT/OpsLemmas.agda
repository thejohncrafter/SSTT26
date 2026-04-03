
open import OpsNotation
open import HEq
open import Either

open import TT.Syntax
open import TT.HEq
open import TT.Telescope

module TT.OpsLemmas where

wkn-trm-of-var⊕trm
  : {d : Dim} {Γ : Ctx} (A : Typ Γ d) (x : Var Γ d ⊕ Trm Γ d) (σ : Wkn Γ)
  → trm-of-var⊕trm A x [ σ ] ≅ trm-of-var⊕trm (A [ σ ]) (x [ σ ])
wkn-trm-of-var⊕trm A (inl v) σ = refl
wkn-trm-of-var⊕trm A (inr t) σ = refl

sub-trm-of-var⊕trm
  : {d : Dim} {Γ : Ctx} (A : Typ Γ d) (x : Var Γ d ⊕ Trm Γ d) (σ : Sub Γ)
  → trm-of-var⊕trm A x [ σ ] ≅ trm-of-var⊕trm (A [ σ ]) (x [ σ ])
sub-trm-of-var⊕trm A (inl v) σ = refl
sub-trm-of-var⊕trm A (inr t) σ = refl

rew-trm-of-var⊕trm
  : {d : Dim} {Γ : Ctx} (A : Typ Γ d) (x : Var Γ d ⊕ Trm Γ d) (σ : Rew Γ)
  → trm-of-var⊕trm A x [ σ ] ≅ trm-of-var⊕trm (A [ σ ]) (x [ σ ])
rew-trm-of-var⊕trm A (inl v) σ = refl
rew-trm-of-var⊕trm A (inr t) σ = refl

nxt-wkn-ctx
  : {d₀ : Dim}
  → (Δ : Ctx)
  → {Γ : Ctx} (σ : Wkn Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → Δ [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ Δ [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-wkn-var
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (v : Var Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → v [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ v [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-wkn-typ
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (A : Typ Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → A [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ A [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-wkn-trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (t : Trm Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → t [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ t [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-wkn-ctx ◆ σ T 𝟙 = refl
nxt-wkn-ctx (Γ , A) σ T 𝟙 = refl
nxt-wkn-ctx (Γ , A) σ T (te , A) = ≅-ctx-, (nxt-wkn-ctx Γ σ T te) (nxt-wkn-typ A σ T te)

nxt-wkn-var (z {Γ} {d₀} {A})        σ T 𝟙        = refl
nxt-wkn-var (z {Γ} {d₀} {A})        σ T (te , A) = ≅-var-z (nxt-wkn-ctx Γ σ T te) (nxt-wkn-typ A σ T te)
nxt-wkn-var (s {Γ} {d₀} {d₁} {A} v) σ T 𝟙        = refl
nxt-wkn-var (s {Γ} {d₀} {d₁} {A} v) σ T (te , A) = ≅-var-s (nxt-wkn-ctx Γ σ T te) (nxt-wkn-typ A σ T te) (nxt-wkn-var v σ T te)

nxt-wkn-typ (Π {Γ} A F) σ T te = ≅-typ-Π (nxt-wkn-ctx Γ σ T te) (nxt-wkn-typ A σ T te) (nxt-wkn-typ F σ T (te , A))
nxt-wkn-typ (U {Γ} d)   σ T te = ≅-typ-U (nxt-wkn-ctx Γ σ T te)
nxt-wkn-typ (E {Γ} d t) σ T te = ≅-typ-E (nxt-wkn-ctx Γ σ T te) (nxt-wkn-trm t σ T te)

nxt-wkn-typ (≃ {Γ} A t u) σ T te = ≅-typ-≃ (nxt-wkn-ctx Γ σ T te) (nxt-wkn-typ A σ T te) (nxt-wkn-trm t σ T te) (nxt-wkn-trm u σ T te)

nxt-wkn-trm (` {Γ} A v)       σ T te = ≅-trm-` (nxt-wkn-ctx Γ σ T te) (nxt-wkn-typ A σ T te) (nxt-wkn-var v σ T te)
nxt-wkn-trm (ƛ {Γ} A F f)     σ T te = ≅-trm-ƛ (nxt-wkn-ctx Γ σ T te) (nxt-wkn-typ A σ T te) (nxt-wkn-typ F σ T (te , A)) (nxt-wkn-trm f σ T (te , A))
nxt-wkn-trm (· {Γ} A F f B t) σ T te = ≅-trm-· (nxt-wkn-ctx Γ σ T te) (nxt-wkn-typ A σ T te) (nxt-wkn-typ F σ T (te , A)) (nxt-wkn-trm f σ T te) (nxt-wkn-typ B σ T te) (nxt-wkn-trm t σ T te)

nxt-wkn-trm (≃rfl {Γ} A t)                    σ T te = ≅-trm-≃rfl (nxt-wkn-ctx Γ σ T te) (nxt-wkn-typ A σ T te) (nxt-wkn-trm t σ T te)
nxt-wkn-trm (≃ind {d} {Γ} A₁ A₂ t₁ t₂ F f u p) σ T te =
  ≅-trm-≃ind
    (nxt-wkn-ctx Γ σ T te)
    (nxt-wkn-typ A₁ σ T te) (nxt-wkn-typ A₂ σ T (te , _))
    (nxt-wkn-trm t₁ σ T te) (nxt-wkn-trm t₂ σ T (te , _))
    (nxt-wkn-typ F σ T (te , _ , _))
    (nxt-wkn-trm f σ T te)
    (nxt-wkn-trm u σ T te) (nxt-wkn-trm p σ T te)

nxt-wkn-var⊕trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (x : Var Δ d₁ ⊕ Trm Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → x [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ x [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]
nxt-wkn-var⊕trm {d₀} {d₁} {Γ} (inl v) σ T te = ≅-var⊕trm-inl (nxt-wkn-ctx Γ σ T te) (nxt-wkn-var v σ T te)
nxt-wkn-var⊕trm {d₀} {d₁} {Γ} (inr t) σ T te = ≅-var⊕trm-inr (nxt-wkn-ctx Γ σ T te) (nxt-wkn-trm t σ T te)

nxt-sub-ctx
  : {d₀ : Dim}
  → (Δ : Ctx)
  → {Γ : Ctx} (σ : Sub Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → Δ [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ Δ [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-sub-var
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (v : Var Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → v [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ v [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-sub-typ
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (A : Typ Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → A [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ A [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-sub-trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (t : Trm Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → t [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ t [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-sub-ctx ◆ σ T 𝟙 = refl
nxt-sub-ctx (Γ , A) σ T 𝟙 = refl
nxt-sub-ctx (Γ , A) σ T (te , A) = ≅-ctx-, (nxt-sub-ctx Γ σ T te) (nxt-sub-typ A σ T te)

nxt-sub-var (z {Γ} {d₀} {A})        σ T 𝟙        = refl
nxt-sub-var (z {Γ} {d₀} {A})        σ T (te , A) = ≅-var⊕trm-inl (≅-ctx-, (nxt-sub-ctx Γ σ T te) (nxt-sub-typ A σ T te)) (≅-var-z (nxt-sub-ctx Γ σ T te) (nxt-sub-typ A σ T te))
nxt-sub-var (s {Γ} {d₀} {d₁} {A} v) σ T 𝟙        = refl
nxt-sub-var (s {Γ} {d₀} {d₁} {A} v) σ T (te , A) =
  begin
    v [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T) ] [ wkn (A [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T) ]) ]
  ≅⟨ ≅-wkn-var⊕trm (nxt-sub-ctx Γ σ T te) (nxt-sub-var v σ T te) (≅-wkn-wkn (nxt-sub-ctx Γ σ T te) (nxt-sub-typ A σ T te)) ⟩
    v [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ] [ wkn (A [ tele te σ ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]) ]
  ≅⟨ ≅-symm (nxt-wkn-var⊕trm _ _ _ 𝟙) ⟩
    v [ tele te σ ] [ wkn (A [ tele te σ ]) ] [ tele (te [ σ ]) (wkn (T [ σ ])) , A [ tele te σ ] ]
  ∎

nxt-sub-typ (Π {Γ} A F) σ T te = ≅-typ-Π (nxt-sub-ctx Γ σ T te) (nxt-sub-typ A σ T te) (nxt-sub-typ F σ T (te , A))
nxt-sub-typ (U {Γ} d)   σ T te = ≅-typ-U (nxt-sub-ctx Γ σ T te)
nxt-sub-typ (E {Γ} d t) σ T te = ≅-typ-E (nxt-sub-ctx Γ σ T te) (nxt-sub-trm t σ T te)

nxt-sub-typ (≃ {Γ} A t u) σ T te = ≅-typ-≃ (nxt-sub-ctx Γ σ T te) (nxt-sub-typ A σ T te) (nxt-sub-trm t σ T te) (nxt-sub-trm u σ T te)

nxt-sub-trm (` {Γ} A v)       σ T te =
  begin
    trm-of-var⊕trm
      (A [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T) ])
      (v [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T) ])
  ≅⟨ ≅-trm-of-var⊕trm (nxt-sub-ctx Γ σ T te) (nxt-sub-typ A σ T te) (nxt-sub-var v σ T te) ⟩
    trm-of-var⊕trm
      (A [ tele te σ ] [ tele (te [ σ ]) (wkn (T [ σ ])) ])
      (v [ tele te σ ] [ tele (te [ σ ]) (wkn (T [ σ ])) ])
  ≅⟨ ≅-symm (wkn-trm-of-var⊕trm (A [ tele te σ ]) (v [ tele te σ ]) _) ⟩
    trm-of-var⊕trm (A [ tele te σ ]) (v [ tele te σ ]) [ tele (te [ σ ]) (wkn (T [ σ ])) ]
  ∎
nxt-sub-trm (ƛ {Γ} A F f)     σ T te = ≅-trm-ƛ (nxt-sub-ctx Γ σ T te) (nxt-sub-typ A σ T te) (nxt-sub-typ F σ T (te , A)) (nxt-sub-trm f σ T (te , A))
nxt-sub-trm (· {Γ} A F f B t) σ T te = ≅-trm-· (nxt-sub-ctx Γ σ T te) (nxt-sub-typ A σ T te) (nxt-sub-typ F σ T (te , A)) (nxt-sub-trm f σ T te) (nxt-sub-typ B σ T te) (nxt-sub-trm t σ T te)

nxt-sub-trm (≃rfl {Γ} A t)                     σ T te = ≅-trm-≃rfl (nxt-sub-ctx Γ σ T te) (nxt-sub-typ A σ T te) (nxt-sub-trm t σ T te)
nxt-sub-trm (≃ind {d} {Γ} A₁ A₂ t₁ t₂ F f u p) σ T te =
  ≅-trm-≃ind
    (nxt-sub-ctx Γ σ T te)
    (nxt-sub-typ A₁ σ T te) (nxt-sub-typ A₂ σ T (te , _))
    (nxt-sub-trm t₁ σ T te) (nxt-sub-trm t₂ σ T (te , _))
    (nxt-sub-typ F σ T (te , _ , _))
    (nxt-sub-trm f σ T te)
    (nxt-sub-trm u σ T te) (nxt-sub-trm p σ T te)

nxt-sub-var⊕trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (x : Var Δ d₁ ⊕ Trm Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → x [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ x [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]
nxt-sub-var⊕trm {d₀} {d₁} {Γ} (inl v) σ T te = nxt-sub-var v σ T te
nxt-sub-var⊕trm {d₀} {d₁} {Γ} (inr t) σ T te = ≅-var⊕trm-inr (nxt-sub-ctx Γ σ T te) (nxt-sub-trm t σ T te)

nxt-rew-ctx
  : {d₀ : Dim}
  → (Δ : Ctx)
  → {Γ : Ctx} (σ : Rew Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → Δ [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ Δ [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-rew-var
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (v : Var Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → v [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ v [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-rew-typ
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (A : Typ Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → A [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ A [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-rew-trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (t : Trm Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → t [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ t [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]

nxt-rew-ctx ◆ σ T 𝟙 = refl
nxt-rew-ctx (Γ , A) σ T 𝟙 = refl
nxt-rew-ctx (Γ , A) σ T (te , A) = ≅-ctx-, (nxt-rew-ctx Γ σ T te) (nxt-rew-typ A σ T te)

nxt-rew-var (z {Γ} {d₀} {A})        σ T 𝟙        = refl
nxt-rew-var (z {Γ} {d₀} {A})        σ T (te , A) = ≅-var-z (nxt-rew-ctx Γ σ T te) (nxt-rew-typ A σ T te)
nxt-rew-var (s {Γ} {d₀} {d₁} {A} v) σ T 𝟙        = refl
nxt-rew-var (s {Γ} {d₀} {d₁} {A} v) σ T (te , A) = ≅-var-s (nxt-rew-ctx Γ σ T te) (nxt-rew-typ A σ T te) (nxt-rew-var v σ T te)

nxt-rew-typ (Π {Γ} A F) σ T te = ≅-typ-Π (nxt-rew-ctx Γ σ T te) (nxt-rew-typ A σ T te) (nxt-rew-typ F σ T (te , A))
nxt-rew-typ (U {Γ} d)   σ T te = ≅-typ-U (nxt-rew-ctx Γ σ T te)
nxt-rew-typ (E {Γ} d t) σ T te = ≅-typ-E (nxt-rew-ctx Γ σ T te) (nxt-rew-trm t σ T te)

nxt-rew-typ (≃ {Γ} A t u) σ T te = ≅-typ-≃ (nxt-rew-ctx Γ σ T te) (nxt-rew-typ A σ T te) (nxt-rew-trm t σ T te) (nxt-rew-trm u σ T te)

nxt-rew-trm (` {Γ} A v)       σ T te = ≅-trm-` (nxt-rew-ctx Γ σ T te) (nxt-rew-typ A σ T te) (nxt-rew-var v σ T te)
nxt-rew-trm (ƛ {Γ} A F f)     σ T te = ≅-trm-ƛ (nxt-rew-ctx Γ σ T te) (nxt-rew-typ A σ T te) (nxt-rew-typ F σ T (te , A)) (nxt-rew-trm f σ T (te , A))
nxt-rew-trm (· {Γ} A F f B t) σ T te = ≅-trm-· (nxt-rew-ctx Γ σ T te) (nxt-rew-typ A σ T te) (nxt-rew-typ F σ T (te , A)) (nxt-rew-trm f σ T te) (nxt-rew-typ B σ T te) (nxt-rew-trm t σ T te)

nxt-rew-trm (≃rfl {Γ} A t)                     σ T te = ≅-trm-≃rfl (nxt-rew-ctx Γ σ T te) (nxt-rew-typ A σ T te) (nxt-rew-trm t σ T te)
nxt-rew-trm (≃ind {d} {Γ} A₁ A₂ t₁ t₂ F f u p) σ T te =
  ≅-trm-≃ind
    (nxt-rew-ctx Γ σ T te)
    (nxt-rew-typ A₁ σ T te) (nxt-rew-typ A₂ σ T (te , _))
    (nxt-rew-trm t₁ σ T te) (nxt-rew-trm t₂ σ T (te , _))
    (nxt-rew-typ F σ T (te , _ , _))
    (nxt-rew-trm f σ T te)
    (nxt-rew-trm u σ T te) (nxt-rew-trm p σ T te)

nxt-rew-var⊕trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (x : Var Δ d₁ ⊕ Trm Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → x [ tele te (wkn T) ] [ tele (te [ wkn T ]) (σ , T)     ]
  ≅ x [ tele te σ       ] [ tele (te [ σ ]) (wkn (T [ σ ])) ]
nxt-rew-var⊕trm {d₀} {d₁} {Γ} (inl v) σ T te = ≅-var⊕trm-inl (nxt-rew-ctx Γ σ T te) (nxt-rew-var v σ T te)
nxt-rew-var⊕trm {d₀} {d₁} {Γ} (inr t) σ T te = ≅-var⊕trm-inr (nxt-rew-ctx Γ σ T te) (nxt-rew-trm t σ T te)

wkn-sub-ctx
  : {d₀ : Dim}
  → (Δ : Ctx)
  → {Γ : Ctx} (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope Γ Δ)
  → Δ [ tele te (wkn T) ] [ tele (te [ wkn T ]) (sub u) ]
  ≅ Δ

wkn-sub-var
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (v : Var Δ d₁)
  → {Γ : Ctx} (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope Γ Δ)
  → v [ tele te (wkn T) ] [ tele (te [ wkn T ]) (sub u) ]
  ≅ inl {Var Δ d₁} {Trm Δ d₁} v

wkn-sub-typ
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (A : Typ Δ d₁)
  → {Γ : Ctx} (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope Γ Δ)
  → A [ tele te (wkn T) ] [ tele (te [ wkn T ]) (sub u) ]
  ≅ A

wkn-sub-trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (t : Trm Δ d₁)
  → {Γ : Ctx} (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope Γ Δ)
  → t [ tele te (wkn T) ] [ tele (te [ wkn T ]) (sub u) ]
  ≅ t

wkn-sub-ctx ◆       T u 𝟙        = refl
wkn-sub-ctx (Γ , A) T u 𝟙        = refl
wkn-sub-ctx (Γ , A) T u (te , A) = ≅-ctx-, (wkn-sub-ctx Γ T u te) (wkn-sub-typ A T u te)

wkn-sub-var (z {Γ} {d₀} {A})        T u 𝟙        = refl
wkn-sub-var (z {Γ} {d₀} {A})        T u (te , A) = ≅-var⊕trm-inl (≅-ctx-, (wkn-sub-ctx Γ T u te) (wkn-sub-typ A T u te)) (≅-var-z (wkn-sub-ctx Γ T u te) (wkn-sub-typ A T u te))
wkn-sub-var (s {Γ} {d₀} {d₁} {A} v) T u 𝟙        = refl
wkn-sub-var (s {Γ} {d₀} {d₁} {A} v) T u (te , A) =
  begin
    v [ tele te (wkn T) ] [ tele (te [ wkn T ]) (sub u) ] [ wkn (A [ tele te (wkn T) ] [ tele (te [ wkn T ]) (sub u) ]) ]
  ≅⟨ ≅-wkn-var⊕trm (wkn-sub-ctx Γ T u te) (wkn-sub-var v T u te) (≅-wkn-wkn (wkn-sub-ctx Γ T u te) (wkn-sub-typ A T u te)) ⟩
    inl v                                                 [ wkn A ]
  ∎

wkn-sub-typ (Π {Γ} A F) T u te = ≅-typ-Π (wkn-sub-ctx Γ T u te) (wkn-sub-typ A T u te) (wkn-sub-typ F T u (te , A))
wkn-sub-typ (U {Γ} d)   T u te = ≅-typ-U (wkn-sub-ctx Γ T u te)
wkn-sub-typ (E {Γ} d t) T u te = ≅-typ-E (wkn-sub-ctx Γ T u te) (wkn-sub-trm t T u te)

wkn-sub-typ (≃ {Γ} A t₁ t₂) T u te = ≅-typ-≃ (wkn-sub-ctx Γ T u te) (wkn-sub-typ A T u te) (wkn-sub-trm t₁ T u te) (wkn-sub-trm t₂ T u te)

wkn-sub-trm (` {Γ} A v)       T u te =
  begin
    trm-of-var⊕trm
      (A [ tele te (wkn T) ] [ tele (te [ wkn T ]) (sub u) ])
      (v [ tele te (wkn T) ] [ tele (te [ wkn T ]) (sub u) ])
  ≅⟨ ≅-trm-of-var⊕trm (wkn-sub-ctx Γ T u te) (wkn-sub-typ A T u te) (wkn-sub-var v T u te) ⟩
    ` A v
  ∎
wkn-sub-trm (ƛ {Γ} A F f)     T u te = ≅-trm-ƛ (wkn-sub-ctx Γ T u te) (wkn-sub-typ A T u te) (wkn-sub-typ F T u (te , A)) (wkn-sub-trm f T u (te , A))
wkn-sub-trm (· {Γ} A F f B t) T u te = ≅-trm-· (wkn-sub-ctx Γ T u te) (wkn-sub-typ A T u te) (wkn-sub-typ F T u (te , A)) (wkn-sub-trm f T u te) (wkn-sub-typ B T u te) (wkn-sub-trm t T u te)

wkn-sub-trm (≃rfl {Γ} A t)                     T u te = ≅-trm-≃rfl (wkn-sub-ctx Γ T u te) (wkn-sub-typ A T u te) (wkn-sub-trm t T u te)
wkn-sub-trm (≃ind {d} {Γ} A₁ A₂ t₁ t₂ F f ω p) T u te =
  ≅-trm-≃ind
    (wkn-sub-ctx Γ T u te)
    (wkn-sub-typ A₁ T u te) (wkn-sub-typ A₂ T u (te , _))
    (wkn-sub-trm t₁ T u te) (wkn-sub-trm t₂ T u (te , _))
    (wkn-sub-typ F T u (te , _ , _))
    (wkn-sub-trm f T u te)
    (wkn-sub-trm ω T u te) (wkn-sub-trm p T u te)

wkn-sub-var⊕trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (x : Var Δ d₁ ⊕ Trm Δ d₁)
  → {Γ : Ctx} (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope Γ Δ)
  → x [ tele te (wkn T) ] [ tele (te [ wkn T ]) (sub u) ]
  ≅ x
wkn-sub-var⊕trm {d₀} {d₁} {Γ} (inl v) T u te = wkn-sub-var v T u te
wkn-sub-var⊕trm {d₀} {d₁} {Γ} (inr t) T u te = ≅-var⊕trm-inr (wkn-sub-ctx Γ T u te) (wkn-sub-trm t T u te)

sub-wkn-ctx
  : {d₀ : Dim}
  → (Δ : Ctx)
  → {Γ : Ctx} (σ : Wkn Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → Δ [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ Δ [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-wkn-var
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (v : Var Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → v [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ v [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-wkn-typ
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (A : Typ Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → A [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ A [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-wkn-trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (t : Trm Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → t [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ t [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-wkn-ctx (Γ , A) σ T u 𝟙        = refl
sub-wkn-ctx (Γ , A) σ T u (te , A) = ≅-ctx-, (sub-wkn-ctx Γ σ T u te) (sub-wkn-typ A σ T u te)

sub-wkn-var (z {Γ} {d₀} {A})        σ T u 𝟙        = refl
sub-wkn-var (z {Γ} {d₀} {A})        σ T u (te , A) = ≅-var⊕trm-inl (≅-ctx-, (sub-wkn-ctx Γ σ T u te) (sub-wkn-typ A σ T u te)) (≅-var-z (sub-wkn-ctx Γ σ T u te) (sub-wkn-typ A σ T u te))
sub-wkn-var (s {Γ} {d₀} {d₁} {A} v) σ T u 𝟙        = refl
sub-wkn-var (s {Γ} {d₀} {d₁} {A} v) σ T u (te , A) =
  begin
    v [ tele te (sub u) ] [ wkn (A [ tele te (sub u) ])         ] [ tele (te [ sub u ]) σ , A [ tele te (sub u) ] ]
  ≅⟨ nxt-wkn-var⊕trm (v [ tele te (sub u) ]) (tele (te [ sub u ]) σ) (A [ tele te (sub u) ]) 𝟙 ⟩
    v [ tele te (sub u) ] [ tele (te [ sub u ]) σ               ] [ wkn (A [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]) ]
  ≅⟨ ≅-wkn-var⊕trm (sub-wkn-ctx Γ σ T u te) (sub-wkn-var v σ T u te) (≅-wkn-wkn (sub-wkn-ctx Γ σ T u te) (sub-wkn-typ A σ T u te)) ⟩
    v [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ] [ wkn (A [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]) ]
  ∎

sub-wkn-typ (Π {Γ} A F) σ T u te = ≅-typ-Π (sub-wkn-ctx Γ σ T u te) (sub-wkn-typ A σ T u te) (sub-wkn-typ F σ T u (te , A))
sub-wkn-typ (U {Γ} d)   σ T u te = ≅-typ-U (sub-wkn-ctx Γ σ T u te)
sub-wkn-typ (E {Γ} d t) σ T u te = ≅-typ-E (sub-wkn-ctx Γ σ T u te) (sub-wkn-trm t σ T u te)

sub-wkn-typ (≃ {Γ} A t₁ t₂) σ T u te = ≅-typ-≃ (sub-wkn-ctx Γ σ T u te) (sub-wkn-typ A σ T u te) (sub-wkn-trm t₁ σ T u te) (sub-wkn-trm t₂ σ T u te)

sub-wkn-trm (` {Γ} A v)       σ T u te =
  begin
    trm-of-var⊕trm (A [ tele te (sub u) ]) (v [ tele te (sub u) ]) [ tele (te [ sub u ]) σ ]
  ≅⟨ wkn-trm-of-var⊕trm (A [ tele te (sub u) ]) (v [ tele te (sub u) ]) _ ⟩
    trm-of-var⊕trm
      (A [ tele te (sub u) ] [ tele (te [ sub u ]) σ ])
      (v [ tele te (sub u) ] [ tele (te [ sub u ]) σ ])
  ≅⟨ ≅-trm-of-var⊕trm (sub-wkn-ctx Γ σ T u te) (sub-wkn-typ A σ T u te) (sub-wkn-var v σ T u te) ⟩
    trm-of-var⊕trm
      (A [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ])
      (v [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ])
  ∎
sub-wkn-trm (ƛ {Γ} A F f)     σ T u te = ≅-trm-ƛ (sub-wkn-ctx Γ σ T u te) (sub-wkn-typ A σ T u te) (sub-wkn-typ F σ T u (te , A)) (sub-wkn-trm f σ T u (te , A))
sub-wkn-trm (· {Γ} A F f B t) σ T u te = ≅-trm-· (sub-wkn-ctx Γ σ T u te) (sub-wkn-typ A σ T u te) (sub-wkn-typ F σ T u (te , A)) (sub-wkn-trm f σ T u te) (sub-wkn-typ B σ T u te) (sub-wkn-trm t σ T u te)

sub-wkn-trm (≃rfl {Γ} A t)                     σ T u te = ≅-trm-≃rfl (sub-wkn-ctx Γ σ T u te) (sub-wkn-typ A σ T u te) (sub-wkn-trm t σ T u te)
sub-wkn-trm (≃ind {d} {Γ} A₁ A₂ t₁ t₂ F f ω p) σ T u te =
  ≅-trm-≃ind
    (sub-wkn-ctx Γ σ T u te)
    (sub-wkn-typ A₁ σ T u te) (sub-wkn-typ A₂ σ T u (te , _))
    (sub-wkn-trm t₁ σ T u te) (sub-wkn-trm t₂ σ T u (te , _))
    (sub-wkn-typ F σ T u (te , _ , _))
    (sub-wkn-trm f σ T u te)
    (sub-wkn-trm ω σ T u te) (sub-wkn-trm p σ T u te)

sub-wkn-var⊕trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (x : Var Δ d₁ ⊕ Trm Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → x [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ x [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]
sub-wkn-var⊕trm {d₀} {d₁} {Γ} (inl v) σ T u te = sub-wkn-var v σ T u te
sub-wkn-var⊕trm {d₀} {d₁} {Γ} (inr t) σ T u te = ≅-var⊕trm-inr (sub-wkn-ctx Γ σ T u te) (sub-wkn-trm t σ T u te)

sub-sub-ctx
  : {d₀ : Dim}
  → (Δ : Ctx)
  → {Γ : Ctx} (σ : Sub Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → Δ [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ Δ [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-sub-var
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (v : Var Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → v [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ v [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-sub-typ
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (A : Typ Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → A [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ A [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-sub-trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (t : Trm Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → t [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ t [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-sub-ctx (Γ , A) σ T u 𝟙        = refl
sub-sub-ctx (Γ , A) σ T u (te , A) = ≅-ctx-, (sub-sub-ctx Γ σ T u te) (sub-sub-typ A σ T u te)

sub-sub-var (z {Γ} {d₀} {A})        σ T u 𝟙        = refl
sub-sub-var (z {Γ} {d₀} {A})        σ T u (te , A) = ≅-var⊕trm-inl (≅-ctx-, (sub-sub-ctx Γ σ T u te) (sub-sub-typ A σ T u te)) (≅-var-z (sub-sub-ctx Γ σ T u te) (sub-sub-typ A σ T u te))
sub-sub-var (s {Γ} {d₀} {d₁} {A} v) σ T u 𝟙        = ≅-symm (wkn-sub-var⊕trm _ _ _ 𝟙)
sub-sub-var (s {Γ} {d₀} {d₁} {A} v) σ T u (te , A) =
  begin
    v [ tele te (sub u) ] [ wkn (A [ tele te (sub u) ])         ] [ tele (te [ sub u ]) σ , A [ tele te (sub u) ] ]
  ≅⟨ nxt-sub-var⊕trm (v [ tele te (sub u) ]) _ _ 𝟙 ⟩
    v [ tele te (sub u) ] [ tele (te [ sub u ]) σ               ] [ wkn (A [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]) ]
  ≅⟨ ≅-wkn-var⊕trm (sub-sub-ctx Γ σ T u te) (sub-sub-var v σ T u te) (≅-wkn-wkn (sub-sub-ctx Γ σ T u te) (sub-sub-typ A σ T u te)) ⟩
    v [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ] [ wkn (A [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]) ]
  ≅⟨ ≅-symm (nxt-sub-var⊕trm (v [ tele te (σ , T) ]) _ _ 𝟙) ⟩
    v [ tele te (σ , T) ] [ wkn (A [ tele te (σ , T) ])         ] [ tele (te [ σ , T ]) (sub (u [ σ ])) , A [ tele te (σ , T) ] ]
  ∎

sub-sub-typ (Π {Γ} A F) σ T u te = ≅-typ-Π (sub-sub-ctx Γ σ T u te) (sub-sub-typ A σ T u te) (sub-sub-typ F σ T u (te , A))
sub-sub-typ (U {Γ} d)   σ T u te = ≅-typ-U (sub-sub-ctx Γ σ T u te)
sub-sub-typ (E {Γ} d t) σ T u te = ≅-typ-E (sub-sub-ctx Γ σ T u te) (sub-sub-trm t σ T u te)

sub-sub-typ (≃ {Γ} A t₁ t₂) σ T u te = ≅-typ-≃ (sub-sub-ctx Γ σ T u te) (sub-sub-typ A σ T u te) (sub-sub-trm t₁ σ T u te) (sub-sub-trm t₂ σ T u te)

sub-sub-trm (` {Γ} A v)       σ T u te =
  begin
    trm-of-var⊕trm (A [ tele te (sub u) ]) (v [ tele te (sub u) ]) [ tele (te [ sub u ]) σ ]
  ≅⟨ sub-trm-of-var⊕trm (A [ tele te (sub u) ]) (v [ tele te (sub u) ]) _ ⟩
    trm-of-var⊕trm
      (A [ tele te (sub u) ] [ tele (te [ sub u ]) σ ])
      (v [ tele te (sub u) ] [ tele (te [ sub u ]) σ ])
  ≅⟨ ≅-trm-of-var⊕trm (sub-sub-ctx Γ σ T u te) (sub-sub-typ A σ T u te) (sub-sub-var v σ T u te) ⟩
    trm-of-var⊕trm
      (A [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ])
      (v [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ])
  ≅⟨ ≅-symm (sub-trm-of-var⊕trm (A [ tele te (σ , T) ]) (v [ tele te (σ , T) ]) _) ⟩
    trm-of-var⊕trm (A [ tele te (σ , T) ]) (v [ tele te (σ , T) ]) [ tele (te [ σ , T ]) (sub (u [ σ ])) ]
  ∎
sub-sub-trm (ƛ {Γ} A F f)     σ T u te = ≅-trm-ƛ (sub-sub-ctx Γ σ T u te) (sub-sub-typ A σ T u te) (sub-sub-typ F σ T u (te , A)) (sub-sub-trm f σ T u (te , A))
sub-sub-trm (· {Γ} A F f B t) σ T u te = ≅-trm-· (sub-sub-ctx Γ σ T u te) (sub-sub-typ A σ T u te) (sub-sub-typ F σ T u (te , A)) (sub-sub-trm f σ T u te) (sub-sub-typ B σ T u te) (sub-sub-trm t σ T u te)

sub-sub-trm (≃rfl {Γ} A t)                     σ T u te = ≅-trm-≃rfl (sub-sub-ctx Γ σ T u te) (sub-sub-typ A σ T u te) (sub-sub-trm t σ T u te)
sub-sub-trm (≃ind {d} {Γ} A₁ A₂ t₁ t₂ F f ω p) σ T u te =
  ≅-trm-≃ind
    (sub-sub-ctx Γ σ T u te)
    (sub-sub-typ A₁ σ T u te) (sub-sub-typ A₂ σ T u (te , _))
    (sub-sub-trm t₁ σ T u te) (sub-sub-trm t₂ σ T u (te , _))
    (sub-sub-typ F σ T u (te , _ , _))
    (sub-sub-trm f σ T u te)
    (sub-sub-trm ω σ T u te) (sub-sub-trm p σ T u te)

sub-sub-var⊕trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (x : Var Δ d₁ ⊕ Trm Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → x [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ x [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]
sub-sub-var⊕trm {d₀} {d₁} {Γ} (inl v) σ T u te = sub-sub-var v σ T u te
sub-sub-var⊕trm {d₀} {d₁} {Γ} (inr t) σ T u te = ≅-var⊕trm-inr (sub-sub-ctx Γ σ T u te) (sub-sub-trm t σ T u te)

sub-rew-ctx
  : {d₀ : Dim}
  → (Δ : Ctx)
  → {Γ : Ctx} (σ : Rew Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → Δ [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ Δ [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-rew-var
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (v : Var Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → v [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ v [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-rew-typ
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (A : Typ Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → A [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ A [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-rew-trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (t : Trm Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → t [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ t [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]

sub-rew-ctx (Γ , A) σ T u 𝟙        = refl
sub-rew-ctx (Γ , A) σ T u (te , A) = ≅-ctx-, (sub-rew-ctx Γ σ T u te) (sub-rew-typ A σ T u te)

sub-rew-var (z {Γ} {d₀} {A})        σ T u 𝟙        = refl
sub-rew-var (z {Γ} {d₀} {A})        σ T u (te , A) = ≅-var⊕trm-inl (≅-ctx-, (sub-rew-ctx Γ σ T u te) (sub-rew-typ A σ T u te)) (≅-var-z (sub-rew-ctx Γ σ T u te) (sub-rew-typ A σ T u te))
sub-rew-var (s {Γ} {d₀} {d₁} {A} v) σ T u 𝟙        = refl
sub-rew-var (s {Γ} {d₀} {d₁} {A} v) σ T u (te , A) =
  begin
    v [ tele te (sub u) ] [ wkn (A [ tele te (sub u) ])         ] [ tele (te [ sub u ]) σ , A [ tele te (sub u) ] ]
  ≅⟨ nxt-rew-var⊕trm (v [ tele te (sub u) ]) (tele (te [ sub u ]) σ) (A [ tele te (sub u) ]) 𝟙 ⟩
    v [ tele te (sub u) ] [ tele (te [ sub u ]) σ               ] [ wkn (A [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]) ]
  ≅⟨ ≅-wkn-var⊕trm (sub-rew-ctx Γ σ T u te) (sub-rew-var v σ T u te) (≅-wkn-wkn (sub-rew-ctx Γ σ T u te) (sub-rew-typ A σ T u te)) ⟩
    v [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ] [ wkn (A [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]) ]
  ∎

sub-rew-typ (Π {Γ} A F) σ T u te = ≅-typ-Π (sub-rew-ctx Γ σ T u te) (sub-rew-typ A σ T u te) (sub-rew-typ F σ T u (te , A))
sub-rew-typ (U {Γ} d)   σ T u te = ≅-typ-U (sub-rew-ctx Γ σ T u te)
sub-rew-typ (E {Γ} d t) σ T u te = ≅-typ-E (sub-rew-ctx Γ σ T u te) (sub-rew-trm t σ T u te)

sub-rew-typ (≃ {Γ} A t₁ t₂) σ T u te = ≅-typ-≃ (sub-rew-ctx Γ σ T u te) (sub-rew-typ A σ T u te) (sub-rew-trm t₁ σ T u te) (sub-rew-trm t₂ σ T u te)

sub-rew-trm (` {Γ} A v)       σ T u te =
  begin
    trm-of-var⊕trm (A [ tele te (sub u) ]) (v [ tele te (sub u) ]) [ tele (te [ sub u ]) σ ]
  ≅⟨ rew-trm-of-var⊕trm (A [ tele te (sub u) ]) (v [ tele te (sub u) ]) _ ⟩
    trm-of-var⊕trm
      (A [ tele te (sub u) ] [ tele (te [ sub u ]) σ ])
      (v [ tele te (sub u) ] [ tele (te [ sub u ]) σ ])
  ≅⟨ ≅-trm-of-var⊕trm (sub-rew-ctx Γ σ T u te) (sub-rew-typ A σ T u te) (sub-rew-var v σ T u te) ⟩
    trm-of-var⊕trm
      (A [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ])
      (v [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ])
  ∎
sub-rew-trm (ƛ {Γ} A F f)     σ T u te = ≅-trm-ƛ (sub-rew-ctx Γ σ T u te) (sub-rew-typ A σ T u te) (sub-rew-typ F σ T u (te , A)) (sub-rew-trm f σ T u (te , A))
sub-rew-trm (· {Γ} A F f B t) σ T u te = ≅-trm-· (sub-rew-ctx Γ σ T u te) (sub-rew-typ A σ T u te) (sub-rew-typ F σ T u (te , A)) (sub-rew-trm f σ T u te) (sub-rew-typ B σ T u te) (sub-rew-trm t σ T u te)

sub-rew-trm (≃rfl {Γ} A t)                     σ T u te = ≅-trm-≃rfl (sub-rew-ctx Γ σ T u te) (sub-rew-typ A σ T u te) (sub-rew-trm t σ T u te)
sub-rew-trm (≃ind {d} {Γ} A₁ A₂ t₁ t₂ F f ω p) σ T u te =
  ≅-trm-≃ind
    (sub-rew-ctx Γ σ T u te)
    (sub-rew-typ A₁ σ T u te) (sub-rew-typ A₂ σ T u (te , _))
    (sub-rew-trm t₁ σ T u te) (sub-rew-trm t₂ σ T u (te , _))
    (sub-rew-typ F σ T u (te , _ , _))
    (sub-rew-trm f σ T u te)
    (sub-rew-trm ω σ T u te) (sub-rew-trm p σ T u te)

sub-rew-var⊕trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (x : Var Δ  d₁ ⊕ Trm Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T : Typ Γ d₀) (u : Trm Γ d₀)
  → (te : Telescope (Γ , T) Δ)
  → x [ tele te (sub u) ] [ tele (te [ sub u ]) σ ]
  ≅ x [ tele te (σ , T) ] [ tele (te [ σ , T ]) (sub (u [ σ ])) ]
sub-rew-var⊕trm {d₀} {d₁} {Γ} (inl v) σ T u te = sub-rew-var v σ T u te
sub-rew-var⊕trm {d₀} {d₁} {Γ} (inr t) σ T u te = ≅-var⊕trm-inr (sub-rew-ctx Γ σ T u te) (sub-rew-trm t σ T u te)

wkn-rew-ctx
  : {d₀ : Dim}
  → (Δ : Ctx)
  → {Γ : Ctx} (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → Δ [ tele te (wkn T₁) ] [ tele (te [ wkn T₁ ]) (rew T₁ T₂) ]
  ≅ Δ [ tele te (wkn T₂) ]

wkn-rew-var
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (v : Var Δ d₁)
  → {Γ : Ctx} (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → v [ tele te (wkn T₁) ] [ tele (te [ wkn T₁ ]) (rew T₁ T₂) ]
  ≅ v [ tele te (wkn T₂) ]

wkn-rew-typ
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (A : Typ Δ d₁)
  → {Γ : Ctx} (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → A [ tele te (wkn T₁) ] [ tele (te [ wkn T₁ ]) (rew T₁ T₂) ]
  ≅ A [ tele te (wkn T₂) ]

wkn-rew-trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (t : Trm Δ d₁)
  → {Γ : Ctx} (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → t [ tele te (wkn T₁) ] [ tele (te [ wkn T₁ ]) (rew T₁ T₂) ]
  ≅ t [ tele te (wkn T₂) ]

wkn-rew-ctx Γ       T₁ T₂ 𝟙        = refl
wkn-rew-ctx (Γ , A) T₁ T₂ (te , A) = ≅-ctx-, (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-typ A T₁ T₂ te)

wkn-rew-var (z {Γ} {d₀} {A})        T₁ T₂ 𝟙        = refl
wkn-rew-var (z {Γ} {d₀} {A})        T₁ T₂ (te , A) = ≅-var-z (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-typ A T₁ T₂ te)
wkn-rew-var (s {Γ} {d₀} {d₁} {A} v) T₁ T₂ 𝟙        = refl
wkn-rew-var (s {Γ} {d₀} {d₁} {A} v) T₁ T₂ (te , A) = ≅-var-s (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-typ A T₁ T₂ te) (wkn-rew-var v T₁ T₂ te)

wkn-rew-typ (Π {Γ} A F) T₁ T₂ te = ≅-typ-Π (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-typ A T₁ T₂ te) (wkn-rew-typ F T₁ T₂ (te , A))
wkn-rew-typ (U {Γ} d)   T₁ T₂ te = ≅-typ-U (wkn-rew-ctx Γ T₁ T₂ te)
wkn-rew-typ (E {Γ} d t) T₁ T₂ te = ≅-typ-E (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-trm t T₁ T₂ te)

wkn-rew-typ (≃ {Γ} A t₁ t₂) T₁ T₂ te = ≅-typ-≃ (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-typ A T₁ T₂ te) (wkn-rew-trm t₁ T₁ T₂ te) (wkn-rew-trm t₂ T₁ T₂ te)

wkn-rew-trm (` {Γ} A v)       T₁ T₂ te = ≅-trm-` (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-typ A T₁ T₂ te) (wkn-rew-var v T₁ T₂ te)
wkn-rew-trm (ƛ {Γ} A F f)     T₁ T₂ te = ≅-trm-ƛ (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-typ A T₁ T₂ te) (wkn-rew-typ F T₁ T₂ (te , A)) (wkn-rew-trm f T₁ T₂ (te , A))
wkn-rew-trm (· {Γ} A F f B t) T₁ T₂ te = ≅-trm-· (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-typ A T₁ T₂ te) (wkn-rew-typ F T₁ T₂ (te , A)) (wkn-rew-trm f T₁ T₂ te) (wkn-rew-typ B T₁ T₂ te) (wkn-rew-trm t T₁ T₂ te)

wkn-rew-trm (≃rfl {Γ} A t)                     T₁ T₂ te = ≅-trm-≃rfl (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-typ A T₁ T₂ te) (wkn-rew-trm t T₁ T₂ te)
wkn-rew-trm (≃ind {d} {Γ} A₁ A₂ t₁ t₂ F f ω p) T₁ T₂ te =
  ≅-trm-≃ind
    (wkn-rew-ctx Γ T₁ T₂ te)
    (wkn-rew-typ A₁ T₁ T₂ te) (wkn-rew-typ A₂ T₁ T₂ (te , _))
    (wkn-rew-trm t₁ T₁ T₂ te) (wkn-rew-trm t₂ T₁ T₂ (te , _))
    (wkn-rew-typ F T₁ T₂ (te , _ , _))
    (wkn-rew-trm f T₁ T₂ te)
    (wkn-rew-trm ω T₁ T₂ te) (wkn-rew-trm p T₁ T₂ te)

wkn-rew-var⊕trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (x : Var Δ d₁ ⊕ Trm Δ d₁)
  → {Γ : Ctx} (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope Γ Δ)
  → x [ tele te (wkn T₁) ] [ tele (te [ wkn T₁ ]) (rew T₁ T₂) ]
  ≅ x [ tele te (wkn T₂) ]
wkn-rew-var⊕trm {d₀} {d₁} {Γ} (inl v) T₁ T₂ te = ≅-var⊕trm-inl (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-var v T₁ T₂ te)
wkn-rew-var⊕trm {d₀} {d₁} {Γ} (inr t) T₁ T₂ te = ≅-var⊕trm-inr (wkn-rew-ctx Γ T₁ T₂ te) (wkn-rew-trm t T₁ T₂ te)

rew-wkn-ctx
  : {d₀ : Dim}
  → (Δ : Ctx)
  → {Γ : Ctx} (σ : Wkn Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → Δ [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ Δ [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-wkn-var
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (v : Var Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → v [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ v [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-wkn-typ
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (A : Typ Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → A [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ A [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-wkn-trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (t : Trm Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → t [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ t [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-wkn-ctx (Γ , T₁) σ T₁ T₂ 𝟙        = refl
rew-wkn-ctx (Γ , A ) σ T₁ T₂ (te , A) = ≅-ctx-, (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-typ A σ T₁ T₂ te)

rew-wkn-var (z {Γ} {d₀} {A})        σ T₁ T₂ 𝟙        = refl
rew-wkn-var (z {Γ} {d₀} {A})        σ T₁ T₂ (te , A) = ≅-var-z (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-typ A σ T₁ T₂ te)
rew-wkn-var (s {Γ} {d₀} {d₁} {A} v) σ T₁ T₂ 𝟙        = refl
rew-wkn-var (s {Γ} {d₀} {d₁} {A} v) σ T₁ T₂ (te , A) = ≅-var-s (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-typ A σ T₁ T₂ te) (rew-wkn-var v σ T₁ T₂ te)

rew-wkn-typ (Π {Γ} A F) σ T₁ T₂ te = ≅-typ-Π (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-typ A σ T₁ T₂ te) (rew-wkn-typ F σ T₁ T₂ (te , A))
rew-wkn-typ (U {Γ} d)   σ T₁ T₂ te = ≅-typ-U (rew-wkn-ctx Γ σ T₁ T₂ te)
rew-wkn-typ (E {Γ} d t) σ T₁ T₂ te = ≅-typ-E (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-trm t σ T₁ T₂ te)

rew-wkn-typ (≃ {Γ} A t₁ t₂) σ T₁ T₂ te = ≅-typ-≃ (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-typ A σ T₁ T₂ te) (rew-wkn-trm t₁ σ T₁ T₂ te) (rew-wkn-trm t₂ σ T₁ T₂ te)

rew-wkn-trm (` {Γ} A v)       σ T₁ T₂ te = ≅-trm-` (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-typ A σ T₁ T₂ te) (rew-wkn-var v σ T₁ T₂ te)
rew-wkn-trm (ƛ {Γ} A F f)     σ T₁ T₂ te = ≅-trm-ƛ (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-typ A σ T₁ T₂ te) (rew-wkn-typ F σ T₁ T₂ (te , A)) (rew-wkn-trm f σ T₁ T₂ (te , A))
rew-wkn-trm (· {Γ} A F f B t) σ T₁ T₂ te = ≅-trm-· (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-typ A σ T₁ T₂ te) (rew-wkn-typ F σ T₁ T₂ (te , A)) (rew-wkn-trm f σ T₁ T₂ te) (rew-wkn-typ B σ T₁ T₂ te) (rew-wkn-trm t σ T₁ T₂ te)

rew-wkn-trm (≃rfl {Γ} A t)                     σ T₁ T₂ te = ≅-trm-≃rfl (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-typ A σ T₁ T₂ te) (rew-wkn-trm t σ T₁ T₂ te)
rew-wkn-trm (≃ind {d} {Γ} A₁ A₂ t₁ t₂ F f ω p) σ T₁ T₂ te =
  ≅-trm-≃ind
    (rew-wkn-ctx Γ σ T₁ T₂ te)
    (rew-wkn-typ A₁ σ T₁ T₂ te) (rew-wkn-typ A₂ σ T₁ T₂ (te , _))
    (rew-wkn-trm t₁ σ T₁ T₂ te) (rew-wkn-trm t₂ σ T₁ T₂ (te , _))
    (rew-wkn-typ F σ T₁ T₂ (te , _ , _))
    (rew-wkn-trm f σ T₁ T₂ te)
    (rew-wkn-trm ω σ T₁ T₂ te) (rew-wkn-trm p σ T₁ T₂ te)

rew-wkn-var⊕trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (x : Var Δ d₁ ⊕ Trm Δ d₁)
  → {Γ : Ctx} (σ : Wkn Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → x [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ x [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]
rew-wkn-var⊕trm {d₀} {d₁} {Γ} (inl v) σ T₁ T₂ te = ≅-var⊕trm-inl (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-var v σ T₁ T₂ te)
rew-wkn-var⊕trm {d₀} {d₁} {Γ} (inr t) σ T₁ T₂ te = ≅-var⊕trm-inr (rew-wkn-ctx Γ σ T₁ T₂ te) (rew-wkn-trm t σ T₁ T₂ te)

rew-sub-ctx
  : {d₀ : Dim}
  → (Δ : Ctx)
  → {Γ : Ctx} (σ : Sub Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → Δ [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ Δ [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-sub-var
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (v : Var Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → v [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ v [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-sub-typ
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (A : Typ Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → A [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ A [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-sub-trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (t : Trm Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → t [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ t [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-sub-ctx (Γ , T₁) σ T₁ T₂ 𝟙        = refl
rew-sub-ctx (Γ , A ) σ T₁ T₂ (te , A) = ≅-ctx-, (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-typ A σ T₁ T₂ te)

rew-sub-var (z {Γ} {d₀} {A})        σ T₁ T₂ 𝟙        = refl
rew-sub-var (z {Γ} {d₀} {A})        σ T₁ T₂ (te , A) = ≅-var⊕trm-inl (≅-ctx-, (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-typ A σ T₁ T₂ te)) (≅-var-z (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-typ A σ T₁ T₂ te))
rew-sub-var (s {Γ} {d₀} {d₁} {A} v) σ T₁ T₂ 𝟙
  rewrite ≡-of-≅ (wkn-rew-var⊕trm (v [ σ ]) (A [ σ ]) (T₂ [ σ ]) 𝟙)
  = refl
rew-sub-var (s {Γ} {d₀} {d₁} {A} v) σ T₁ T₂ (te , A) =
  begin
    v [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂)                 ] [ wkn (A [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]) ]
  ≅⟨ ≅-wkn-var⊕trm (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-var v σ T₁ T₂ te) (≅-wkn-wkn (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-typ A σ T₁ T₂ te)) ⟩
    v [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ] [ wkn (A [ tele te (σ , T₁) ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]) ]
  ≅⟨ ≅-symm (nxt-rew-var⊕trm _ _ _ 𝟙) ⟩
    v [ tele te (σ , T₁)    ] [ wkn (A [ tele te (σ , T₁) ])                     ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) , A [ tele te (σ , T₁) ] ]
  ∎

rew-sub-typ (Π {Γ} A F) σ T₁ T₂ te = ≅-typ-Π (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-typ A σ T₁ T₂ te) (rew-sub-typ F σ T₁ T₂ (te , A))
rew-sub-typ (U {Γ} d)   σ T₁ T₂ te = ≅-typ-U (rew-sub-ctx Γ σ T₁ T₂ te)
rew-sub-typ (E {Γ} d t) σ T₁ T₂ te = ≅-typ-E (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-trm t σ T₁ T₂ te)

rew-sub-typ (≃ {Γ} A t₁ t₂) σ T₁ T₂ te = ≅-typ-≃ (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-typ A σ T₁ T₂ te) (rew-sub-trm t₁ σ T₁ T₂ te) (rew-sub-trm t₂ σ T₁ T₂ te)

rew-sub-trm (` {Γ} A v)       σ T₁ T₂ te =
  begin
    trm-of-var⊕trm
      (A [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ])
      (v [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ])
  ≅⟨ ≅-trm-of-var⊕trm (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-typ A σ T₁ T₂ te) (rew-sub-var v σ T₁ T₂ te) ⟩
    trm-of-var⊕trm
      (A [ tele te (σ , T₁) ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ])
      (v [ tele te (σ , T₁) ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ])
  ≅⟨ ≅-symm (rew-trm-of-var⊕trm (A [ tele te (σ , T₁) ]) (v [ tele te (σ , T₁) ]) _) ⟩
    trm-of-var⊕trm
      (A [ tele te (σ , T₁) ])
      (v [ tele te (σ , T₁) ])
    [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]
  ∎
rew-sub-trm (ƛ {Γ} A F f)     σ T₁ T₂ te = ≅-trm-ƛ (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-typ A σ T₁ T₂ te) (rew-sub-typ F σ T₁ T₂ (te , A)) (rew-sub-trm f σ T₁ T₂ (te , A))
rew-sub-trm (· {Γ} A F f B t) σ T₁ T₂ te = ≅-trm-· (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-typ A σ T₁ T₂ te) (rew-sub-typ F σ T₁ T₂ (te , A)) (rew-sub-trm f σ T₁ T₂ te) (rew-sub-typ B σ T₁ T₂ te) (rew-sub-trm t σ T₁ T₂ te)

rew-sub-trm (≃rfl {Γ} A t)                     σ T₁ T₂ te = ≅-trm-≃rfl (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-typ A σ T₁ T₂ te) (rew-sub-trm t σ T₁ T₂ te)
rew-sub-trm (≃ind {d} {Γ} A₁ A₂ t₁ t₂ F f ω p) σ T₁ T₂ te =
  ≅-trm-≃ind
    (rew-sub-ctx Γ σ T₁ T₂ te)
    (rew-sub-typ A₁ σ T₁ T₂ te) (rew-sub-typ A₂ σ T₁ T₂ (te , _))
    (rew-sub-trm t₁ σ T₁ T₂ te) (rew-sub-trm t₂ σ T₁ T₂ (te , _))
    (rew-sub-typ F σ T₁ T₂ (te , _ , _))
    (rew-sub-trm f σ T₁ T₂ te)
    (rew-sub-trm ω σ T₁ T₂ te) (rew-sub-trm p σ T₁ T₂ te)

rew-sub-var⊕trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (x : Var Δ d₁ ⊕ Trm Δ d₁)
  → {Γ : Ctx} (σ : Sub Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → x [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ x [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]
rew-sub-var⊕trm {d₀} {d₁} {Γ} (inl v) σ T₁ T₂ te = rew-sub-var v σ T₁ T₂ te
rew-sub-var⊕trm {d₀} {d₁} {Γ} (inr t) σ T₁ T₂ te = ≅-var⊕trm-inr (rew-sub-ctx Γ σ T₁ T₂ te) (rew-sub-trm t σ T₁ T₂ te)

rew-rew-ctx
  : {d₀ : Dim}
  → (Δ : Ctx)
  → {Γ : Ctx} (σ : Rew Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → Δ [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ Δ [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-rew-var
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (v : Var Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → v [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ v [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-rew-typ
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (A : Typ Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → A [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ A [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-rew-trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (t : Trm Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → t [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ t [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]

rew-rew-ctx (Γ , T₁) σ T₁ T₂ 𝟙        = refl
rew-rew-ctx (Γ , A ) σ T₁ T₂ (te , A) = ≅-ctx-, (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-typ A σ T₁ T₂ te)

rew-rew-var (z {Γ} {d₀} {A})        σ T₁ T₂ 𝟙        = refl
rew-rew-var (z {Γ} {d₀} {A})        σ T₁ T₂ (te , A) = ≅-var-z (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-typ A σ T₁ T₂ te)
rew-rew-var (s {Γ} {d₀} {d₁} {A} v) σ T₁ T₂ 𝟙        = refl
rew-rew-var (s {Γ} {d₀} {d₁} {A} v) σ T₁ T₂ (te , A) = ≅-var-s (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-typ A σ T₁ T₂ te) (rew-rew-var v σ T₁ T₂ te)

rew-rew-typ (Π {Γ} A F) σ T₁ T₂ te = ≅-typ-Π (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-typ A σ T₁ T₂ te) (rew-rew-typ F σ T₁ T₂ (te , A))
rew-rew-typ (U {Γ} d)   σ T₁ T₂ te = ≅-typ-U (rew-rew-ctx Γ σ T₁ T₂ te)
rew-rew-typ (E {Γ} d t) σ T₁ T₂ te = ≅-typ-E (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-trm t σ T₁ T₂ te)

rew-rew-typ (≃ {Γ} A t₁ t₂) σ T₁ T₂ te = ≅-typ-≃ (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-typ A σ T₁ T₂ te) (rew-rew-trm t₁ σ T₁ T₂ te) (rew-rew-trm t₂ σ T₁ T₂ te)

rew-rew-trm (` {Γ} A v)       σ T₁ T₂ te = ≅-trm-` (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-typ A σ T₁ T₂ te) (rew-rew-var v σ T₁ T₂ te)
rew-rew-trm (ƛ {Γ} A F f)     σ T₁ T₂ te = ≅-trm-ƛ (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-typ A σ T₁ T₂ te) (rew-rew-typ F σ T₁ T₂ (te , A)) (rew-rew-trm f σ T₁ T₂ (te , A))
rew-rew-trm (· {Γ} A F f B t) σ T₁ T₂ te = ≅-trm-· (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-typ A σ T₁ T₂ te) (rew-rew-typ F σ T₁ T₂ (te , A)) (rew-rew-trm f σ T₁ T₂ te) (rew-rew-typ B σ T₁ T₂ te) (rew-rew-trm t σ T₁ T₂ te)

rew-rew-trm (≃rfl {Γ} A t)                  σ T₁ T₂ te = ≅-trm-≃rfl (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-typ A σ T₁ T₂ te) (rew-rew-trm t σ T₁ T₂ te)
rew-rew-trm (≃ind {d} {Γ} A₁ A₂ t₁ t₂ F f ω p) σ T₁ T₂ te =
  ≅-trm-≃ind
    (rew-rew-ctx Γ σ T₁ T₂ te)
    (rew-rew-typ A₁ σ T₁ T₂ te) (rew-rew-typ A₂ σ T₁ T₂ (te , _))
    (rew-rew-trm t₁ σ T₁ T₂ te) (rew-rew-trm t₂ σ T₁ T₂ (te , _))
    (rew-rew-typ F σ T₁ T₂ (te , _ , _))
    (rew-rew-trm f σ T₁ T₂ te)
    (rew-rew-trm ω σ T₁ T₂ te) (rew-rew-trm p σ T₁ T₂ te)

rew-rew-var⊕trm
  : {d₀ d₁ : Dim}
  → {Δ : Ctx} (x : Var Δ d₁ ⊕ Trm Δ d₁)
  → {Γ : Ctx} (σ : Rew Γ) (T₁ T₂ : Typ Γ d₀)
  → (te : Telescope (Γ , T₁) Δ)
  → x [ tele te (rew T₁ T₂) ] [ tele (te [ rew T₁ T₂ ]) (σ , T₂) ]
  ≅ x [ tele te (σ , T₁)    ] [ tele (te [ σ , T₁ ]) (rew (T₁ [ σ ]) (T₂ [ σ ])) ]
rew-rew-var⊕trm {d₀} {d₁} {Γ} (inl v) σ T₁ T₂ te = ≅-var⊕trm-inl (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-var v σ T₁ T₂ te)
rew-rew-var⊕trm {d₀} {d₁} {Γ} (inr t) σ T₁ T₂ te = ≅-var⊕trm-inr (rew-rew-ctx Γ σ T₁ T₂ te) (rew-rew-trm t σ T₁ T₂ te)
