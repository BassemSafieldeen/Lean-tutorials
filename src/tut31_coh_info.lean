import tut13_ptrace
import tut28_entropy

--- COHERENT INFORMATION

open_locale tensor_product

noncomputable theory

variables
{ℋ₁ : Type} [complex_hilbert_space ℋ₁]
{ℋ₂ : Type} [complex_hilbert_space ℋ₂]

variable (ρ : (ℋ₁ ⊗[ℂ] ℋ₂) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂))

namespace bipartite -- To use Tr₁ we need to open the namespace that contains it.

def coh_info := entropy(Tr₁(ρ)) - entropy(ρ)
variable {ρ}

@[simp] lemma coh_info_def : coh_info ρ = entropy(Tr₁(ρ)) - entropy(ρ) := rfl

end bipartite