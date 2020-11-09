import tut7

-- Some theorems about unital channels because they look easy.

variables {ℋ₁ : Type} [complex_hilbert_space ℋ₁]
{ℋ₂ : Type} [complex_hilbert_space ℋ₂]

variables (𝒩 : (ℋ₁ →ₗ[ℂ] ℋ₁) →ₗ[ℂ] (ℋ₂ →ₗ[ℂ] ℋ₂)) [quantum_channel 𝒩]

def unital : Prop := 𝒩 (1 : ℋ₁ →ₗ[ℂ] ℋ₁) = (1 : ℋ₂ →ₗ[ℂ] ℋ₂)

