Require Import HoTT.
Require Import polynomial.
Require Import polynomial_lemma.
Require Import it_structure.

Section generic_programming.
  Variable (Y : Type).

  Structure generic_definition :=
    {
      g_const : forall (T : Type), T -> Y ;
      g_prod : Y * Y -> Y ;
      g_left : Y -> Y ;
      g_right : Y -> Y
    }.

  Fixpoint to_spec
           (G : generic_definition)
           (X : Type)
           (P : polynomial)
    : forall (u : poly_act P X), poly_fam P (fun _ : X => Y) u -> Y
    := match P with
       | poly_var => fun _ => idmap
       | poly_const T => fun t _ => g_const G T t
       | poly_times _ _ =>
         fun u x =>
           g_prod G (to_spec G _ _ (fst u) (fst x),
                     to_spec G _ _ (snd u) (snd x))
       | poly_plus _ _ =>
         fun u =>
           match u with
           | inl y =>
             fun x =>
               g_left G (to_spec G _ _ y x)
           | inr y =>
             fun x =>
               g_right G (to_spec G _ _ y x)
           end
       end.

  Variable (Σ : it_signature)
           (T : IT Σ)
           (G : generic_definition).

  Definition extend : T -> Y
    := it_ind (fun _ => Y)
              (fun i u x => to_spec G T (point Σ i) u x).
End generic_programming.

Arguments extend {Y Σ} T G _.

Section example_length.
  Definition generic_length : generic_definition nat
    := {|g_const := fun _ _ => 0 ;
         g_prod := fun n => (Peano.plus (fst n) (snd n).+1) ;
         g_left := idmap ;
         g_right := idmap|}.

  Variable (A : Type).

  Definition list_signature : it_signature
    := {|point_index := Unit ;
         point := fun _ => const Unit + (const A * [-])|}.

  Definition nil {T : IT list_signature} : T
    := it_point (it_alg _ T) tt (inl tt).

  Definition cons {T : IT list_signature} (a : A) (t : T) : T
    := it_point (it_alg _ T) tt (inr (a,t)).
 
  Variable (T : IT list_signature).

  Definition list_length := extend T generic_length.

  Definition length_nil
    : list_length nil = 0.
  Proof.
    compute.
    rewrite it_ind_beta.
    reflexivity.
  Defined.

  Definition length_cons (a : A) (t : T)
    : list_length (cons a t) = Peano.plus 1 (list_length t).
  Proof.
    compute.
    rewrite it_ind_beta.
    reflexivity.
  Defined.
End example_length.