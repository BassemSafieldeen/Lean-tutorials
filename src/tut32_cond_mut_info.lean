import tut5
import tut28_entropy
import tut30_cond_entropy

open bipartite tripartite

open_locale tensor_product

noncomputable theory

---- CONDITIONAL MUTUAL INFORMATION

variables
{ℋ₁ : Type} [complex_hilbert_space ℋ₁]
{ℋ₂ : Type} [complex_hilbert_space ℋ₂]
{ℋ₃ : Type} [complex_hilbert_space ℋ₃]

variable (ρ : (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂ ⊗[ℂ] ℋ₃))

-- Move these important checks to the ptrace tut?
#check bipartite.Tr₁ ρ -- woah, I did not expect this one to work; especially not like this.
#check tripartite.Tr₁ ρ
#check bipartite.Tr₂ ρ
#check tripartite.Tr₂ ρ
#check tripartite.Tr₃ ρ

#check tripartite.Tr₁₃ ρ
#check tripartite.Tr₁₂ ρ
#check tripartite.Tr₂₃ ρ

/--
cond_entropy(A|C) + cond_entropy(B|C) - cond_entropy(AB|C)
-/
def cond_mut_info :=
cond_entropy(Tr₂ ρ) + cond_entropy(Tr₁ ρ) - (entropy_bp(Tr₃ ρ) - entropy(Tr₁₃ ρ))
variable {ρ}