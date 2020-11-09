import linear_algebra.tensor_product

import tut5
import tut13_ptrace
import tut28_entropy

open_locale tensor_product

noncomputable theory

---- QUANTUM ENTROPY

variables {ℋ : Type} [complex_hilbert_space ℋ]
{ℋ₁ : Type} [complex_hilbert_space ℋ₁]
{ℋ₂ : Type} [complex_hilbert_space ℋ₂]


variable (ρ : (ℋ₁ ⊗[ℂ] ℋ₂) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂))

open bipartite

def mut_info : ℝ := entropy(Tr₂ ρ) + entropy(Tr₁ ρ) - entropy(ρ)
variable {ρ}

@[simp] lemma mut_info_def : 
mut_info ρ =  entropy(Tr₂ ρ) + entropy(Tr₁ ρ) - entropy(ρ) := rfl

theorem mut_info_nonneg : mut_info ρ ≥ 0 := 
begin
    simp only [mut_info_def, entropy_def],
    sorry,
end