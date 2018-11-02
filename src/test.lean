import category_theory.category group_theory.group_action category_theory.functor
import category_theory.yoneda

open category_theory category_theory.category
instance Gset (G : Type) [group G] :
  category (Σ X : Type, {f : G → X → X // is_group_action f}) :=
{ hom := λ X Y, {k : X.1 → Y.1 // ∀ (g : G) (x : X.1), k (X.2.1 g x) = Y.2.1 g (k x) },
  id := λ X, ⟨id, λ g x, rfl⟩,
  comp := λ X Y Z h₁ h₂, ⟨h₂.1 ∘ h₁.1, by simp [h₁.2, h₂.2] at *⟩ }


/- given ctegories D and C i watnt to give for each object X in C a functo from D to C
-/
def const_func (D C : Type*) [category D][category C](X:C): functor D C:=
    {obj:=λ_,X ,
     map' := λ _ _ _, category.id X }

def const_nat {D C : Type*} [category D] [category C] {X Y : C} (f : hom X Y) :
  const_func D C X ⟹ const_func D C Y :=
{ app := λ _, f,
  naturality' := by dsimp [const_func]; simp }

/- given a functor F :D → C I'm going to give a functor from Cᵒᵖ to Type 
sending X to Hom(const_func X,F) 
-/
def chris_func (D C:Type*)[category D][category C](F:functor D C): functor (Cᵒᵖ) (Type*) :=
{ obj := λ X, const_func D C X ⟹ F,
  map' := λ X Y f, ((yoneda (D ⥤ C)).obj F).map (const_nat f),
  map_id' := λ X, funext $ λ x, nat_trans.ext _ _ $ λ Z, id_comp _ _,
  map_comp' := λ X Y Z f g, funext $ λ h, nat_trans.ext _ _ $ λ Z, assoc _ _ _ _
}
/- given a functor F: D ⥤ C limit will give me an obect X:C  -/
structure limit (D :Type*){C : Type*}[category D][category C](F:D ⥤ C):=
(limit:C)
(is_limit: (chris_func D C F) ≅ (yoneda C).obj limit)

/-now to give an instance of a category for fibred product diagram-/
inductive three_stuff :Type 
|B 
|U
|F 

inductive fiber_diagram.hom : three_stuff → three_stuff → Type
| id : Π u, fiber_diagram.hom u u
| cov_map : fiber_diagram.hom three_stuff.U three_stuff.B
| moduli : fiber_diagram.hom three_stuff.F three_stuff.B

def fiber_diagram.hom.comp : Π {X Y Z: three_stuff}, fiber_diagram.hom X Y → 
fiber_diagram.hom Y Z → fiber_diagram.hom X Z
| _ _ _ (fiber_diagram.hom.id u) g := g
|three_stuff.U three_stuff.B three_stuff.B hom.cov_map (hom.id three_stuff.B):=fiber_diagram.hom.cov_map
|three_stuff.F three_stuff.B three_stuff.B hom.moduli (hom.id three_stuff.B):=fiber_diagram.hom.moduli




instance fiber_diagram :category three_stuff :=
{ hom := fiber_diagram.hom,
  id := fiber_diagram.hom.id,
  comp :=λ _ _ _ , fiber_diagram.hom.comp,
  id_comp':= λ X Y f,by cases X ;cases f ;refl,
  comp_id':= λ X Y f, by cases Y;cases f;refl,
  assoc':=λ W X Y Z f g h,by cases W;cases Y;cases f;cases g;refl,   
} 
