Require Import HoTT.
Require Import polynomial.

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
     | poly_var => fun _ x => x
     | poly_const _ => fun _ => idmap
     | poly_times _ _ =>
       fun p x => (fam_const (fst p) (fst x), fam_const (snd p) (snd x))
     | poly_plus _ _ =>
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
     | poly_var => fun _ => idpath
     | poly_const _ => fun _ => idpath
     | poly_times _ _ =>
       fun x => path_prod' (fam_const_map f (fst x)) (fam_const_map f (snd x))
     | poly_plus _ _ =>
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
     | poly_var => fun _ z => z
     | poly_const _ => fun _ _ => idpath
     | poly_times _ _ =>
       fun y z => path_prod' (fam_eq f g (fst y) (fst z)) (fam_eq f g (snd y) (snd z))
     | poly_plus _ _ =>
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
     | poly_var => fun x z => z
     | poly_const _ => fun _ => idmap
     | poly_times _ _ => fun x z => (fam_sum (fst x) (fst z), fam_sum (snd x) (snd z))
     | poly_plus _ _ => fun x =>
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
     | poly_var => fun _ => idpath
     | poly_const _ => fun _ => idpath
     | poly_times _ _ => fun x => path_prod' (const_dmap f (fst x)) (const_dmap f (snd x))
     | poly_plus _ _ =>
       fun x =>
         match x with
         | inl xl => ap inl (const_dmap f xl)
         | inr xr => ap inr (const_dmap f xr)
         end
     end.
