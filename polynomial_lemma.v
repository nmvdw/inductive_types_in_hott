Require Import HoTT.
Require Import polynomial.

Open Scope poly_scope.

(* The action of a polynomial on a map is functorial. *)
Fixpoint poly_map_id (P : polynomial) {A : Type}
  : forall (x : poly_act P A), poly_map P idmap x = x
  := match P with
     | [-] => fun _ => idpath
     | const A => fun _ => idpath
     | P₁ * P₂ => fun x => path_prod' (poly_map_id P₁ (fst x)) (poly_map_id P₂ (snd x))
     | P₁ + P₂ =>
       fun x =>
         match x with
         | inl xl => ap inl (poly_map_id P₁ xl)
         | inr xr => ap inr (poly_map_id P₂ xr)
         end
     end.

Fixpoint poly_map_compose
           {P : polynomial} {A B C : Type}
           (g : B -> C) (f : A -> B)
  : forall (x : poly_act P A), poly_map P (g o f) x = poly_map P g (poly_map P f x)
  := match P with
     | [-] => fun _ => idpath
     | const A => fun _ => idpath
     | P₁ * P₂ =>
       fun x => path_prod' (poly_map_compose g f (fst x))
                           (poly_map_compose g f (snd x))
     | P₁ + P₂ =>
       fun x =>
         match x with
         | inl xl => ap inl (poly_map_compose g f xl)
         | inr xr => ap inr (poly_map_compose g f xr)
         end
     end.

Definition transport_pr2
           {A : Type} {F : A -> Type}
           {x z : {z : A & F z}} y
           (p : x.1 = y) (q : x = z)
  : transport F p x.2 = transport F (ap pr1 q^ @ p) z.2
  := match q with
     | idpath => ap (fun z => transport F z x.2) (concat_1p p)^
     end.

Fixpoint fam_const
         {A B : Type}
         {P : polynomial}
  : forall (p : poly_act P A), poly_fam P (fun _ : A => B) p -> poly_act P B
  := match P with
     | [-] => fun _ x => x
     | const A => fun _ => idmap
     | P₁ * P₂ =>
       fun p x => (fam_const (fst p) (fst x), fam_const (snd p) (snd x))
     | P₁ + P₂ =>
       fun p =>
         match p with
         | inl pl => fun x => inl(fam_const pl x)
         | inr pr => fun x => inr(fam_const pr x)
         end
     end.

Fixpoint fam_const_map
           {A B : Type}
           {P : polynomial}
           (f : A -> B)
  : forall (x : poly_act P A), fam_const x (poly_dmap P f x) = poly_map P f x
  := match P with
     | [-] => fun _ => idpath
     | const A => fun _ => idpath
     | P₁ * P₂ =>
       fun x => path_prod' (fam_const_map f (fst x)) (fam_const_map f (snd x))
     | P₁ + P₂ =>
       fun x =>
         match x with
         | inl xl => ap inl (fam_const_map f xl)
         | inr xr => ap inr (fam_const_map f xr)
         end
     end.

Fixpoint fam_eq
           {A B : Type}
           {P : polynomial}
           (f g : A -> B)
  : forall (y : poly_act P A)
           (z : poly_fam P (fun x : A => f x = g x) y),
    poly_map P f y = poly_map P g y
  := match P with
     | [-] => fun _ z => z
     | const A => fun _ _ => idpath
     | P₁ * P₂ =>
       fun y z => path_prod' (fam_eq f g (fst y) (fst z)) (fam_eq f g (snd y) (snd z))
     | P₁ + P₂ =>
       fun y => match y with
                    | inl yl => fun z => ap inl (fam_eq f g yl z)
                    | inr yr => fun z => ap inr (fam_eq f g yr z)
                end
     end.

Fixpoint fam_sum
           {P : polynomial}
           {A : Type}
           {B : A -> Type}
  : forall (x : poly_act P {x : A & B x}),
    poly_fam P (fun z : {x : A & B x} => B z.1) x -> poly_fam P B (poly_map P pr1 x)
  := match P with
     | [-] => fun x z => z
     | const A => fun _ => idmap
     | P₁ * P₂ => fun x z => (fam_sum (fst x) (fst z), fam_sum (snd x) (snd z))
     | P₁ + P₂ => fun x =>
       match x with
       | inl xl => fun z => fam_sum xl z
       | inr xr => fun z => fam_sum xr z
       end
     end.

Fixpoint const_dmap
           {P : polynomial}
           {A B : Type}
           (f : A -> B)
  : forall (x : poly_act P A),
    fam_const x (poly_dmap P f x) = poly_map P f x
  := match P with
     | [-] => fun _ => idpath
     | const A => fun _ => idpath
     | P₁ * P₂ => fun x => path_prod' (const_dmap f (fst x)) (const_dmap f (snd x))
     | P₁ + P₂ =>
       fun x =>
         match x with
         | inl xl => ap inl (const_dmap f xl)
         | inr xr => ap inr (const_dmap f xr)
         end
     end.
