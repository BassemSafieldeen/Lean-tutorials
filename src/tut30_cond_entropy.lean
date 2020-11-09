import linear_algebra.tensor_product

import tut28_entropy
import tut13_ptrace

---- CONDITIONAL ENTROPY

open_locale tensor_product

noncomputable theory

variables
{ℋ₁ : Type*} [complex_hilbert_space ℋ₁]
{ℋ₂ : Type*} [complex_hilbert_space ℋ₂]

variable (ρ : (ℋ₁ ⊗[ℂ] ℋ₂) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂))

namespace bipartite -- when use `open` and when `namespace`?

def cond_entropy := entropy(ρ) - entropy(Tr₁ ρ)
variable {ρ}

@[simp] lemma cond_entropy_def : cond_entropy(ρ) = entropy(ρ) - entropy(Tr₁ ρ) := rfl

/--
Conditioning does not increase entropy:
-/
theorem entropy_ptrace_ge_cond_entropy : 
entropy(Tr₂ ρ) ≥ cond_entropy(ρ) :=
begin
    simp only [cond_entropy_def, ge_iff_le, entropy_def],
    sorry
end

end bipartite