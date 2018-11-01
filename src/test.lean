import category_theory.category group_theory.group_action category_theory.functor
import category_theory.yoneda

open category_theory category_theory.category
instance (G : Type) [group G] :
  category (Σ X : Type, {f : G → X → X // is_group_action f}) :=
{ hom := λ X Y, {k : X.1 → Y.1 // ∀ (g : G) (x : X.1), k (X.2.1 g x) = Y.2.1 g (k x) },
  id := λ X, ⟨id, λ g x, rfl⟩,
  comp := λ X Y Z h₁ h₂, ⟨h₂.1 ∘ h₁.1, by simp [h₁.2, h₂.2] at *⟩ }


/- given ctegories D and C i watnt to give for each object X in C a functo from D to C
-/
def const_func (D : Type*) { C :Type*}[category D][category C](X:C): functor D C:=
    {obj:=λ_,X ,
     map' := λ _ _ _, category.id X }

def const_nat {D C : Type*} [category D] [category C] (X Y : C) (f : hom X Y) :
  const_func D X ⟹ const_func D Y :=
{ app:= λ _, f,
  naturality' := by dsimp [const_func]; simp }

/- given a functor F :D → C I'm going to give a functor from Cᵒᵖ to Type sending X to Hom(const_func X,F)
-/
def chris_func (D C:Type*)[category D][category C](F:functor D C): functor (Cᵒᵖ) (Type*) := 
  {obj := λ X,hom (const_func D X) F,
  map' := λ f, functor.map' (yoneda C) _  --(const_nat f)
}