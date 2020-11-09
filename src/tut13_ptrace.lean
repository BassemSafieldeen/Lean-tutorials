import tut5

-- PARTIAL TRACES

import linear_algebra.tensor_product

open_locale tensor_product

noncomputable theory

variables 
{ℋ₁ : Type*} [complex_hilbert_space ℋ₁] 
{ℋ₂ : Type*} [complex_hilbert_space ℋ₂]
{ℋ₃ : Type*} [complex_hilbert_space ℋ₃]

namespace bipartite

def Tr₁ (ρ : (ℋ₁ ⊗[ℂ] ℋ₂) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) : ℋ₂ →ₗ[ℂ] ℋ₂ := 
{
    to_fun    := sorry,
    map_add'  := sorry,
    map_smul' := sorry,
}

def Tr₂ (ρ : (ℋ₁ ⊗[ℂ] ℋ₂) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) : ℋ₁ →ₗ[ℂ] ℋ₁ := 
{
    to_fun    := sorry,
    map_add'  := sorry,
    map_smul' := sorry,
}

end bipartite

namespace tripartite

def Tr₁ (ρ : (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃)) : ℋ₂ ⊗[ℂ] ℋ₃ →ₗ[ℂ] ℋ₂ ⊗[ℂ] ℋ₃ := 
{
    to_fun    := sorry,
    map_add'  := sorry,
    map_smul' := sorry,
}

def Tr₂ (ρ : (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃)) : ℋ₁ ⊗[ℂ] ℋ₃ →ₗ[ℂ] ℋ₁ ⊗[ℂ] ℋ₃ := 
{
    to_fun    := sorry,
    map_add'  := sorry,
    map_smul' := sorry,
}

def Tr₃ (ρ : (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃)) : (ℋ₁ ⊗[ℂ] ℋ₂) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂) := 
{
    to_fun    := sorry,
    map_add'  := sorry,
    map_smul' := sorry,
}

def Tr₁₂ (ρ : (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃)) : ℋ₃ →ₗ[ℂ] ℋ₃ := 
{
    to_fun    := sorry,
    map_add'  := sorry,
    map_smul' := sorry,
}

def Tr₁₃ (ρ : (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃)) : ℋ₂ →ₗ[ℂ] ℋ₂ := 
{
    to_fun    := sorry,
    map_add'  := sorry,
    map_smul' := sorry,
}

def Tr₂₃ (ρ : (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃)) : ℋ₁ →ₗ[ℂ] ℋ₁ := 
{
    to_fun    := sorry,
    map_add'  := sorry,
    map_smul' := sorry,
}

end tripartite

namespace bipartite

variables (ρ : ℋ₁ →ₗ[ℂ] ℋ₁) [quantum_state ρ]
(σ : ℋ₂ →ₗ[ℂ] ℋ₂) [quantum_state σ]

@[simp] theorem Tr₂_tmul : Tr₁(ρ ⊗ σ) = σ := sorry

@[simp] theorem Tr₁_tmul : Tr₂(ρ ⊗ σ) = ρ := sorry

end bipartite