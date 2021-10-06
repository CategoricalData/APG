(* Coq Formalization of Algebraic Property Graphs, by Ryan Wisnesky. *)

Open Scope type_scope.
Set Implicit Arguments.

Require Import JMeq FunctionalExtensionality 
   ProofIrrelevance Logic.ClassicalEpsilon Setoid.

(* Helper functions ****************************************)

Lemma FnHelper {X Y} (x:X) {P Q:X->Y} 
 (pf: (fun x => P x) = (fun x => Q x)) : P x = Q x.
Proof.
refine (match pf in _ = y return P x = y x with
  | refl_equal => refl_equal
 end).
Qed.

Lemma ExPfIrr {X} {Q:X->Prop} (h1 h2 : { x  | Q x } )
 : (proj1_sig h1 = proj1_sig h2) -> h1 = h2.
Proof.
 intros pf. destruct h1,h2;simpl in *. subst. f_equal. 
 apply proof_irrelevance.
Qed.

Lemma ExistTHelper {A T} a t a0 t0 : 
 a = a0 -> JMeq t t0 -> @existT A T a t = @existT A T a0 t0.
Proof.
 intros pf. subst. intros pf. f_equal. auto. apply JMeq_eq. auto.
Qed.

Lemma EqDecAx {X} (x1 x2 : X) : {x1 = x2} + {x1 <> x2}.
Proof.
 apply excluded_middle_informative.
Qed.
Record Quotient {T} {R: T->T->Prop} (pfA : equivalence T R) := mkQuo {
  Quo : Type;
  eqc : T -> Quo;
  repr: Quo -> T;
  pfResp1 : forall {a b}, R a b -> eqc a = eqc b;
  pfResp2 : forall {p q}, eqc p = eqc q -> R p q;
  pfSurj  : forall q, eqc (repr q) = q;

  pfMake    : forall {X} (f: T -> X) (pf: forall t1 t2, R t1 t2 -> f t1 = f t2), Quo -> X ;
  pfProp    : forall {X} (f: T -> X) (pf: forall t1 t2, R t1 t2 -> f t1 = f t2) 
   (x:T) , (pfMake f pf (eqc x)) = f x;
}.

Definition mapQ {T1 T2 R1 R2} {pf1: equivalence T1 R1} {pf2: equivalence T2 R2}
(Q1 : Quotient pf1)      (Q2 : Quotient pf2) (f: T1 -> T2)
(pf: forall x y, R1 x y -> R2 (f x) (f y)) : Quo Q1 -> Quo Q2.
 apply (pfMake Q1 (fun x => eqc Q2 (f x)) (fun x y pf0 => pfResp1 Q2 (pf x y pf0) )).
Defined.

Axiom axiomQ : forall {T} {R:T->T->Prop} {pf: equivalence T R}, Quotient pf.

(* Category Theory ************************************************* *)

Record Category : Type := newCategory {
 ob : Type;
 hom : ob -> ob -> Type;
 Id : forall {x}, hom x x;
 Comp : forall {x y z}, hom x y -> hom y z -> hom x z;

 catId1  : forall {x y} (f : hom x y), (Comp Id f) = f;
 catId2  : forall {x y} (f : hom x y), Comp f Id = f;
 catComp : forall {w x y z} 
  (f: hom w x) g (h: hom y z), Comp f (Comp g h) = Comp (Comp f g) h;
}.

Definition Ob {C} := ob C.
Definition Hom {C} x y := hom C x y.
Definition id {C} x := @Id C x.
Definition comp {C} {x y z : ob C} (f: Hom x y) (g: Hom y z) := Comp C f g.

Definition terminal {C} (x: ob C) := forall a, exists! (f: Hom a x), True.  
Definition initial  {C} (x: ob C) := forall a, exists! (f: Hom x a), True.
Definition product {C} (X1 X2 X: ob C) (p1 : Hom X X1) (p2 : Hom X X2) :=
 forall Y (f1 : Hom Y X1) (f2 : Hom Y X2), 
  exists! (f: Hom Y X), comp f p1 = f1 /\ comp f p2 = f2.
Definition coproduct {C} (X1 X2 X: ob C) (i1 : Hom X1 X) (i2 : Hom X2 X) :=
 forall Y (f1 : Hom X1 Y) (f2 : Hom X2 Y), 
  exists! (f: Hom X Y), comp i1 f = f1 /\ comp i2 f = f2.
Definition coequalizer {C} (X Y: ob C) (f g: Hom X Y) Q (q : Hom Y Q) := comp f q = comp g q /\
 forall Q0 (q0 : Hom Y Q0),  comp f q0 = comp g q0 ->
  exists! (u: Hom Q Q0), comp q u = q0. 
Definition equalizer {C} (X Y: ob C) (f g: Hom Y X) Q (q : Hom Q Y) := comp q f = comp q g /\
 forall Q0 (q0 : Hom Q0 Y), comp q0 f = comp q0 g ->
  exists! (u: Hom Q0 Q), comp u q = q0.  

(* Functors *****************************)

Record Functor C D := newFunctor {
 ApplyO : ob C -> ob D;
 ApplyF : forall {x y}, hom C x y -> hom D (ApplyO x) (ApplyO y);

 funId : forall {x}, ApplyF (id x) = id (ApplyO x);
 funComp : forall {x y z} (f: hom C x y) (g: hom C y z),
  ApplyF (comp f g) = comp (ApplyF f) (ApplyF g);
}.

Definition applyF {C D} (F: Functor C D) {x y} := @ApplyF C D F x y.
Definition applyO {C D} (F: Functor C D) := @ApplyO C D F .

Definition IdFunctor C : Functor C C. refine ( 
  newFunctor C C (fun x => x) (fun x y f => f) _ _); auto. 
Defined.

Definition CompFunctor {C D E} (F: Functor C D) (G: Functor D E) : Functor C E.
 refine (newFunctor C E (fun x => applyO G (applyO F x))
 (fun _ _ f => applyF G (applyF F f)) _ _).
destruct F,G; compute in *; congruence.
destruct F,G; compute in *; congruence.
Defined.

(* Natural Transformations *****************************)

Record Transform {C D} (F G : Functor C D) := newTransform {
 component : forall x, Hom (applyO F x) (applyO G x);
 natural : forall {x y} (f : hom C x y),
   comp (component x) (applyF G f) = comp (applyF F f) (component y);
}.
Definition Component {C D} {F G : Functor C D} x := @component C D F G x.

Lemma TransPfIrr {C D} {F G : Functor C D} (h1 h2 : Transform F G)
 : (Component h1 = Component h2) -> h1 = h2.
Proof.
 intros pf. destruct h1,h2;simpl in *. subst. f_equal. apply proof_irrelevance.
Qed.

Definition IdTrans {C D} (F: Functor C D) : Transform F F.
refine (newTransform  F F (fun c => id (applyO F c)) _). intros.
unfold comp. rewrite (@catId1 D). rewrite (@catId2 D). constructor. 
Defined.

Definition CompTrans {C D} {F G H: @Functor C D}
 (h1 : Transform F G) (h2: Transform G H) : Transform F H.
refine (newTransform F H (fun c => comp (Component h1 c) (Component h2 c)) _).
intros. unfold comp. 
rewrite (@catComp D). rewrite <- (natural  h1).
rewrite <- (catComp D). rewrite (natural h2).  rewrite (@catComp D).
constructor.
Defined.

(* Examples *****************************)

Definition SET : Category. refine (newCategory  (fun x y => x -> y)
 (fun x => fun y:x => y) (fun x y z f g a => g (f a)) _ _ _).
 constructor. constructor.  constructor. 
Defined.

Definition CSet (C: Category) : Category.
 refine (@newCategory (Functor C SET) (Transform) IdTrans (@CompTrans C SET) _ _ _);
 intros; try apply TransPfIrr; try apply PI; simpl in *;
  apply functional_extensionality_dep ; intros;
 apply functional_extensionality_dep; intros; auto.
Defined.

Theorem SetInitial : @initial SET Empty_set.
Proof.
  intros a. exists (fun x : Empty_set => match x with end).
  split; auto. intros. apply functional_extensionality_dep. 
  intros x; elim x; auto.
Qed.
 
Theorem SetTerminal : @terminal SET unit.
Proof.
  intros a. exists (fun x => tt).
  split; auto. intros. apply functional_extensionality_dep. 
  intros x; destruct (x' x); auto.
Qed.

Theorem SetProduct {X1 X2} : @product SET X1 X2 (X1 * X2) fst snd.
Proof.
 intros X. intros. exists (fun x => (f1 x, f2 x)).
 unfold unique. split; simpl; auto. intros f pf.  
 apply functional_extensionality_dep. 
 intros x. destruct pf. subst. destruct (f x). simpl. auto.
Qed.

Theorem SetCoProduct {X1 X2} : @coproduct SET X1 X2 (X1 + X2) (@inl X1 X2) (@inr X1 X2).
Proof.
 intros X. intros. exists (fun x => match x with inl y => f1 y | inr y => f2 y end).
 unfold unique. split; simpl; auto. intros f pf. destruct pf.  
 apply functional_extensionality_dep. 
 intros x. subst. destruct x; auto.
Qed.

Definition EqualizerHelper {Y Z} (f : Y -> Z) (g : Y -> Z) Q0  
 (q0 : Q0 -> Y)  : forall  
 (pf:(fun a : Q0 => f (q0 a)) = (fun a : Q0 => g (q0 a))) (u : Q0),
      {y : Y | f y = g y}.
intros pf q. exists (q0 q). simpl. refine (
 match pf in _ = y return f (q0 q) = y q with
  | refl_equal => refl_equal
 end 
).
Defined. 

Theorem SetEqualizer {X Y} (f g : Hom Y X) 
 : @equalizer SET X Y f g { y:Y | f y = g y} (fun x => proj1_sig x).
Proof.
 split. simpl. apply functional_extensionality_dep. intros. destruct x; auto. 
 intros. simpl in *. 
 exists (EqualizerHelper f g q0 H). split. split. intros u pf.
 compute. apply functional_extensionality_dep. intros q0'.
 apply ExPfIrr. simpl. subst. auto.
Qed.

Inductive Lift {S T:Type} (f g : S -> T) : T -> T -> Prop :=
| LiftRefl : forall {t}, Lift f g t t
| LiftSym  : forall {t1 t2}, Lift f g t1 t2 -> Lift f g t2 t1
| LiftTrans: forall {t1 t2 t3},  Lift f g t1 t2 -> Lift f g t2 t3 -> Lift f g t1 t3
| LiftInj  : forall {s}, Lift f g (f s) (g s).

Lemma LiftEquiv {S T:Type} (f g : S -> T) : equivalence _ (Lift f g).
Proof.
 split; compute; intros. constructor. exact (LiftTrans H H0). exact (LiftSym H).
Qed.

Definition quotient {S T} (f g : S -> T) := Quo   (@axiomQ _ (Lift f g) (LiftEquiv f g)).
Definition Eqc      {S T} (f g : S -> T) := eqc   (@axiomQ _ (Lift f g) (LiftEquiv f g)).
Definition Repr     {S T} (f g : S -> T) := repr  (@axiomQ _ (Lift f g) (LiftEquiv f g)).

Theorem SetCoEq {X Y} f g 
 : @coequalizer SET X Y f g (quotient f g) (Eqc f g).
Proof.
 split. apply functional_extensionality_dep. 
 intros x. compute in *. destruct (axiomQ  ).  apply pfResp3. apply LiftInj. 
 intros.  exists ( @comp SET _ _ _ (Repr f g) q0 ).
 split.
 apply functional_extensionality_dep. intros y.
 rewrite (catComp SET). simpl in *.
 unfold Repr,Eqc.
 destruct (axiomQ). simpl.
 induction (@pfResp4 (repr0 (eqc0 y)) y).
 auto. etransitivity; eauto. congruence. 
 symmetry. change ((fun a : X => q0 (g a)) s = q0 (f s)).
 rewrite <- H. reflexivity. auto.
 intros u pf. subst. simpl in *.
 unfold Repr,Eqc,quotient in *. compute in *. destruct (axiomQ ).
 apply functional_extensionality_dep. intros q.
 f_equal. apply pfSurj0.
Qed.

(* Types ******************************************)

Section APG.
 Variable B : Type.
 Variable P : B -> Type.

Inductive Ty L :=
 | Zero  : Ty L
 | One   : Ty L
 | Plus  : Ty L -> Ty L -> Ty L
 | Times : Ty L -> Ty L -> Ty L
 | Base  : B    -> Ty L
 | Label : L    -> Ty L.
Fixpoint MapTy {L1 L2} (f: L1 -> @Ty L2) (ty: @Ty L1) : @Ty L2 := 
 match ty with
  | Zero  _     => Zero  _
  | One   _     => One   _
  | Plus  a b => Plus  (MapTy f a) (MapTy f b)
  | Times a b => Times (MapTy f a) (MapTy f b)
  | Label l   => f l
  | Base  _ b   => Base  _ b
 end.

(* Free BCCC ***************************************************)

Inductive term {L} {lam : L -> Ty L} : Ty L -> Ty L -> Type :=
 | ELEM: forall l, term  (Label  l) (lam l)
 | IDEN: forall {t}, term  t t 
 | COMP: forall {s t u}, term  s t -> term  t u -> term  s u
 | PRIM: forall {b} (c: P b), term  (One _) (Base _ b)
 | tT  : forall {t}, term  t (One _)
 | fF  : forall {t}, term  (Zero  _) t 
 | PAIR: forall {s t  t'}, term  s t -> term  s  t'-> term  s (Times  t t')
 | CASE: forall {s s' t }, term  s t -> term  s' t -> term  (Plus  s s') t
 | INL : forall {s t }, term  s (Plus  s t)
 | INR : forall {s t }, term  t (Plus  s t)
 | FST : forall {s t }, term   (Times  s t) s
 | SND : forall {s t }, term   (Times  s t) t.

Inductive termEq {L} {lam : L -> Ty L} : forall {a b}, @term L lam a b -> term a b -> Prop :=
 | termRefl : forall {a b} (t: term a b), termEq t t
 | termSym  : forall {a b} (t1 t2: term a b), 
     termEq t1 t2 -> termEq t2 t1
 | termTrans : forall {a b} (t1 t2 t3: term a b), 
     termEq t1 t2 -> termEq t2 t3 -> termEq t1 t3
 | termCongComp : forall {a b c} (f f0 : term a b) (g g0 : term b c),
    termEq f f0 -> termEq g g0 -> termEq (COMP f g) (COMP f0 g0) 
 | termCongPair : forall {a b c} (f f0 : term a b) (g g0 : term a c),
    termEq f f0 -> termEq g g0 -> termEq (PAIR f g) (PAIR f0 g0) 
 | termCongCase : forall {a b c} (f f0 : term a c) (g g0 : term b c),
    termEq f f0 -> termEq g g0 -> termEq (CASE f g) (CASE f0 g0) 
 | termId1 : forall {a b} (f: term a b), termEq (COMP IDEN f) f
 | termId2 : forall {a b} (f: term a b), termEq (COMP f IDEN) f
 | termAssoc : forall {a b c d} (f: term a b) (g: term b c) (h: term c d),
    termEq (COMP (COMP f g) h) (COMP f (COMP g h))
 | termOne  : forall {a} (t: term a (One _)), termEq t (tT)
 | termZero : forall {a} (t: term (Zero  _) a), termEq t (fF )
 | termTimesBeta1 : forall {a b c} (f: term a b) (g: term a c), 
    termEq (COMP (PAIR f g) FST) f
 | termTimesBeta2 : forall {a b c} (f: term a b) (g: term a c), 
    termEq (COMP (PAIR f g) SND) g
 | termPlusBeta1  : forall {a b c} (f: term b c) (g: term a c), 
    termEq (COMP INL (CASE f g)) f
 | termPlusBeta2  : forall {a b c} (f: term b c) (g: term a c), 
    termEq (COMP INR (CASE f g)) g
 | termTimesEta : forall {a b},
   termEq (PAIR (@FST L lam a b) SND) IDEN
 | termPlusEta  : forall {a b},
   termEq (CASE (@INL L lam a b) INR) IDEN.

Lemma termEquiv {L lam a b} : equivalence _ (@termEq L lam a b).
Proof.
 split; compute; intros. constructor. exact (termTrans H H0). exact (termSym H).
Qed.

Add Parametric Relation {L : Type} {lam} {a b : Ty L}
  : (@term L lam a b) (@termEq L lam a b)
  reflexivity proved by termRefl
  symmetry proved by termSym
  transitivity proved by termTrans
  as parel.
Add Parametric Morphism {L : Type} {lam} {a b c : Ty L} : (@COMP L lam a b c)
  with signature (@termEq L lam a b) ==> (@termEq L lam b c) ==> (@termEq L lam a c) as comp_mor.
Proof.
intros; apply termCongComp; auto.
Qed.
Add Parametric Morphism {L : Type} {lam} {a b c : Ty L} : (@PAIR L lam a b c)
  with signature (@termEq L lam a b) ==> (@termEq L lam a c) ==> (@termEq L lam a (Times b c)) as pair_mor.
Proof.
intros; apply termCongPair; auto.
Qed.
Add Parametric Morphism {L : Type} {lam} {a b c : Ty L} : (@CASE L lam a b c)
  with signature (@termEq L lam a c) ==> (@termEq L lam b c) ==> (@termEq L lam (Plus a b) c) as case_mor.
Proof.
intros; apply termCongCase; auto.
Qed.

Definition termQ {L lam} {f g : Ty L} := Quo  (@axiomQ _ _ (@termEquiv L lam f g)).
Definition termEqc      {L lam} {f g : Ty L} := eqc   (@axiomQ _ _ (@termEquiv L lam f g)).
Definition termRepr     {L lam} {f g : Ty L} := repr  (@axiomQ _ _ (@termEquiv L lam f g)).

Definition freeBCC (L:Type) (lam:L->Ty L) : Category.
refine (@newCategory (Ty L) (@termQ L lam) 
 (fun x => termEqc (@IDEN L lam x)) 
 (fun x y z f g => termEqc (COMP (termRepr f) (termRepr g))) _ _ _);
 intros. compute in *.
 destruct (axiomQ ). destruct (axiomQ ). 
 rewrite <- (pfSurj0 f). apply pfResp3. rewrite (pfSurj0 f).
 rewrite <- (pfResp6 IDEN). apply termId1. auto.
 intros. compute in *. auto. 
 destruct (axiomQ ). destruct (axiomQ ). 
 rewrite <- (pfSurj0 f). apply pfResp3. rewrite (pfSurj0 f).
 rewrite <- (pfResp6 IDEN). apply termId2. auto.
 intros. compute in *.
 destruct (axiomQ  ). destruct (axiomQ  ). 
 destruct (axiomQ  ). destruct (axiomQ  ).
 destruct (axiomQ  ). destruct (axiomQ  ).
 apply pfResp9. rewrite <- (pfResp14 (COMP (repr0 f) (repr1 g))).
 rewrite <- (pfResp12 (COMP (repr1 g) (repr2 h))).
 apply termSym. apply termAssoc. auto. auto.
Defined.

(*************************************************************)
(* Schemas and APGs *)

Record schema := newschema {
 L0 : Type;
 SIGMA : L0 -> Ty L0;
}.

Inductive TERM {L} {lam : L -> Type} : Ty L -> Type :=
 | ID0  : forall l (e : lam l), TERM (Label l)
 | Prim0: forall b (c: P b), TERM (Base _ b)
 | Tt0  : TERM (One _)
 | Pair0: forall {t t'}, TERM t -> TERM t' -> TERM (Times  t t')
 | Inl0 : forall {t t'}, TERM t -> TERM (Plus  t t')
 | Inr0 : forall {t t'}, TERM t'-> TERM (Plus  t t').

Record apg (S: schema) := newapg {
 E0 : L0 S -> Type;
 PHI : forall l (e: E0 l), @TERM (L0 S) E0 (SIGMA S l);
}.

Fixpoint tyToSet {S} (G: apg S) (t: Ty (L0 S)) : Type :=
 match t with
  | Zero _ => Empty_set
  | One _ => unit
  | Plus  a b => (tyToSet G a) + (tyToSet G b)
  | Times  a b => (tyToSet G a) * (tyToSet G b)
  | Label  l => E0 G l
  | Base _ b => P b
  end.

Definition coerce {S}  {G : apg S} {t} 
 (term : @TERM (L0 S) (E0 G) t) : tyToSet G t.
induction term; simpl in *; intros; auto. constructor.
Defined.

Fixpoint termToFn {S} (G: apg S) {a b : Ty (L0 S)} (t: @term (L0 S) (SIGMA S) a b)
 : tyToSet G a -> tyToSet G b :=
 match t in term a0 b0 return @tyToSet S G a0 -> @tyToSet S G b0 with
 | IDEN => fun x => x
 | COMP f g => fun x => termToFn G g (termToFn G f x)
 | PRIM c => fun x => c
 | tT => fun x => tt
 | fF => fun x => match x with end
 | PAIR f g => fun x => (termToFn G f x, termToFn G g x)
 | CASE f g => fun x => match x with | inl w => termToFn G f w | inr w => termToFn G g w end
 | INL => fun x => inl x
 | INR => fun x => inr x
 | FST => fun x => fst x
 | SND => fun x => snd x
 | ELEM l => fun x => coerce (PHI G l x) 
 end.

Lemma termToFnProper {S} (G: apg S) {a b : Ty (L0 S)} (t1 t2: term a b):
 termEq t1 t2 -> termToFn G t1 = termToFn G t2.
Proof.
 intros. apply functional_extensionality_dep.
 induction H; simpl in *; try auto; intros; try apply functional_extensionality_dep; intros.
 rewrite IHtermEq1. rewrite IHtermEq2. auto.
 rewrite (IHtermEq1 x). apply IHtermEq2.
 rewrite IHtermEq1. rewrite IHtermEq2. auto.
 destruct x. apply IHtermEq1. apply IHtermEq2.
 destruct (termToFn G t x). auto.
 elim x. 
 destruct x; auto.
 destruct x; auto.
Qed.

Lemma termToFnProper2 {S} (G: apg S) {a b : Ty (L0 S)} (t1 t2: term a b):
 termEq t1 t2 -> forall z, termToFn G t1 z = termToFn G t2 z.
Proof.
 intros pf z. rewrite (termToFnProper G pf). auto.
Qed.

Add Parametric Morphism {S} (G: apg S) {a b : Ty (L0 S)} : (@termToFn S G a b)
  with signature (@termEq (L0 S) (SIGMA S) a b) ==> (@eq (@tyToSet S G a -> @tyToSet S G b)) as prop_mor.
Proof.
intros; apply termToFnProper; auto.
Qed.

(* Theorem 1: Every APG induces a functor *)

Definition apgToFunctor {S} (G: apg S) : Functor (freeBCC (SIGMA S)) SET.
refine (newFunctor (freeBCC (SIGMA S)) SET 
 (fun a => tyToSet G a) (fun a b f => termToFn G (termRepr f)) _ _).
intros. apply functional_extensionality_dep. intros y.
 destruct S,G. simpl in *. unfold termEqc,termRepr.  
 destruct (axiomQ ). simpl in *.
 assert (termEq (repr0 (eqc0 IDEN)) IDEN). symmetry. 
 apply (pfResp4 IDEN). auto.  
 rewrite (termToFnProper (newapg (newschema SIGMA0) PHI0) H).
 simpl. auto.
intros. apply functional_extensionality_dep. intros w.
 destruct S,G. simpl in *. unfold termEqc,termRepr,termQ in *. simpl in *.
 destruct (axiomQ  ). simpl in *.
 destruct (axiomQ  ). simpl in *.
 destruct (axiomQ  ). simpl in *.
 assert (termEq 
     (repr2
     (eqc2 (COMP (repr0 f) (repr1 g)))) 
      (COMP (repr0 f) (repr1 g))). symmetry. apply pfResp8. auto. 
 rewrite (termToFnProper (newapg (newschema SIGMA0) PHI0) H).
 simpl. auto.
Defined.

Fixpoint MapTERM {L F G t} (h : forall l, F l -> G l)
 (term : @TERM L F t) : @TERM L G t :=
 match term in @TERM _ _ r return @TERM L G r with
 | ID0   l e   => ID0 l (h l e) 
 | Prim0 c => Prim0 c 
 | Tt0        => Tt0 
 | Pair0  x y => Pair0  (MapTERM h x) (MapTERM h y)
 | Inl0   x   => Inl0   (MapTERM h x)
 | Inr0   y   => Inr0   (MapTERM h y)
 end. 

Record apgMorphism {S} (G1 G2: apg S) := newapgMorphism {
 LMAP : forall {l}, E0 G1 l -> E0 G2 l;
 PFNAT : forall {l} e, MapTERM (@LMAP) (PHI G1 l e) = PHI G2 l (LMAP e);
}.

Lemma apgMorphismEq{S} (G1 G2: apg S) (h j : apgMorphism G1 G2) :
 @LMAP S G1 G2 h  = @LMAP S G1 G2 j -> h = j.
Proof.
 intros. destruct G1,G2,h,j. simpl in *. subst. f_equal. apply proof_irrelevance.
Qed.

Definition apgMorphismToNT {S} (G1 G2: apg S) (h: apgMorphism G1 G2)
 (t: Ty (L0 S)) : tyToSet G1 t -> tyToSet G2 t.
intros x. induction t; simpl in *; auto.
destruct x. left. apply IHt1. auto. right. apply IHt2. auto.
exact (IHt1 (fst x), IHt2 (snd x)). apply (LMAP h x).
Defined.

(* Theorem 1: S-APG morphisms induce natural transformations. *)

Definition apgMorphismToNt {S} (G1 G2: apg S) (h: apgMorphism G1 G2)
  : Transform (apgToFunctor G1) (apgToFunctor G2).
refine (newTransform  (apgToFunctor G1) (apgToFunctor G2)
 (apgMorphismToNT h) _).
intros. apply functional_extensionality. intros w. simpl in *.
unfold termQ,termRepr,termEqc in *. 
destruct (axiomQ ). simpl in *.
generalize (repr0 f). clear pfResp3 pfResp4 pfSurj0 repr0 pfProp0 f pfMake0 eqc0.
induction t; simpl in *; auto; try contradiction.
Focus 2. rewrite IHt1. rewrite IHt2. auto. 
Focus 2. rewrite IHt1. rewrite IHt2. auto.
Focus 2. destruct w. rewrite IHt1. auto. rewrite IHt2. auto.
destruct S,G1,G2,h. simpl in *.
 rewrite <- (PFNAT0 l w). generalize PFNAT0. clear PFNAT0. intros.
 induction ((PHI0 l w)); simpl in *; auto; try discriminate; try congruence.
Defined.

Definition IdapgMorphism {S} (G: apg S) : apgMorphism G G.
refine (newapgMorphism G G (fun l e => e) _).
intros. destruct S,G; simpl in *. 
induction (PHI0 l e); simpl in *; auto; try discriminate; try congruence.
Defined.

Definition apgMorphismCompose {S} {G1 G2 G3 : apg S} (F: apgMorphism G1 G2) (G: apgMorphism G2 G3) : apgMorphism G1 G3.
refine (newapgMorphism _ _ (fun l e => LMAP G (LMAP F e)) _).
intros. destruct S,G1,G2,G3,F,G. simpl in *.
rewrite <- (PFNAT1 l (LMAP0 l e)). rewrite <- (PFNAT0 l e). 
simpl. clear PFNAT0 PFNAT1.
induction (PHI0 l e); simpl in *; auto; try discriminate; try congruence.
Defined.

(* Theorem 1: APGs on a schema form a category. *)

Definition apgInst (S: schema) : Category.
refine (
  @newCategory (apg S) (@apgMorphism S) 
 (fun x => IdapgMorphism x)
 (fun x y z f g => apgMorphismCompose f g ) _ _ _ );
 intros; destruct S,x,y; apply apgMorphismEq; auto.
Defined.

Definition Initialapg {S} : apg S := @newapg S
   (fun l => Empty_set) (fun l x => match x with end).
Definition InitialapgMorphism {S} (G: apg S) : apgMorphism Initialapg G.
refine (newapgMorphism Initialapg G 
  (fun l x => match x with end) _).
intros. elim e.
Defined.

Theorem apgInstInitial S : @initial (apgInst S) Initialapg.
Proof.
  intros a. exists (InitialapgMorphism a). 
  split; auto. intros. apply apgMorphismEq. 
  apply functional_extensionality_dep. intros x. elim x'.
  intros. apply functional_extensionality_dep. intros z. elim z.
Qed.

Definition CoProductapg S (G1 G2 : apg S) : apg S.
refine (@newapg S
  (fun l => E0 G1 l + E0 G2 l)
  (fun l (e:E0 G1 l + E0 G2 l) => 
   match e with 
   | inl a => MapTERM (fun l e => inl e) (PHI G1 l a)
   | inr b => MapTERM (fun l e => inr e) (PHI G2 l b)
   end)); auto. 
Defined.

Definition InlapgMorphism {S} (G1 G2: apg S) 
  : apgMorphism G1 (CoProductapg G1 G2).
refine (newapgMorphism G1 (CoProductapg G1 G2) (fun l e => inl e) _).
intros. simpl. auto.
Defined.

Definition InrapgMorphism {S} (G1 G2: apg S) 
  : apgMorphism G2 (CoProductapg G1 G2).
refine (newapgMorphism G2 (CoProductapg G1 G2) (fun l e => inr e) _).
intros. auto.
Defined.

Definition apgCoproduct {S} (X1 X2: apg S)
  Y (f1 : apgMorphism X1 Y) (f2 : apgMorphism X2 Y)
: apgMorphism (CoProductapg X1 X2) Y. 
refine (newapgMorphism (CoProductapg X1 X2) Y  
  (fun l e => match e with 
   | inl a =>  LMAP f1 a
   | inr b =>  LMAP f2 b
   end) _). intros. destruct e; simpl.
 destruct f1,f2. simpl in *. rewrite <- (PFNAT0 l e).
 induction ((PHI X1 l e)); simpl in *; auto.
 congruence. congruence. congruence.
 destruct f1,f2. simpl in *. rewrite <- (PFNAT1 l e).
 induction ((PHI X2 l e)); simpl in *; auto.
 congruence. congruence. congruence.
Defined. 

Theorem apgHasCoProducts {S} {X1 X2 : apg S} : @coproduct (apgInst S) X1 X2 (CoProductapg X1 X2) (InlapgMorphism X1 X2) (InrapgMorphism X1 X2).
 intros X. intros. exists (apgCoproduct f1 f2).
 split. split. 
 apply apgMorphismEq. auto. auto.
 apply apgMorphismEq. auto. auto.
 intros f pf. destruct pf as [pf1 pf2]. 
 subst. simpl. destruct f,S,X1,X2,X; compute in *.
 apply apgMorphismEq. simpl in *.  apply functional_extensionality_dep.
  intros x. apply functional_extensionality_dep.
  intros y; destruct y; auto.
Qed.

Definition FstSim {L E a b} : @TERM L E (Times a b)
 -> @TERM L E a.
intros e. inversion e. exact X.
Defined.
Definition SndSim {L E a b} : @TERM L E (Times a b)
 -> @TERM L E b.
intros e. inversion e. exact X0.
Defined. 
Definition CaseSim {L E a b} : @TERM L E (Plus a b)
 -> @TERM L E a + @TERM L E b.
intros e. inversion e. left. exact X. right. exact X.
Defined. 

Fixpoint termToFnAlt {S} (G: apg S) {a b : Ty (L0 S)} (t: @term (L0 S) (SIGMA S) a b)
 : @TERM (L0 S) (E0 G) a -> @TERM (L0 S) (E0 G) b :=
 match t in term a0 b0 return @TERM (L0 S) (E0 G) a0 -> @TERM (L0 S) (E0 G) b0 with
 | IDEN => fun x => x
 | COMP f g => fun x => termToFnAlt G g (termToFnAlt G f x)
 | PRIM c => fun x => Prim0 c
 | tT => fun x => Tt0
 | fF => fun x => match x with end
 | PAIR f g => fun x => Pair0 (termToFnAlt G f x) (termToFnAlt G g x)
 | CASE f g => fun x => match CaseSim  x with | inl w => termToFnAlt G f w | inr w => termToFnAlt G g w end 
 | INL => fun x => Inl0 x
 | INR => fun x => Inr0 x
 | FST => fun x => FstSim  x
 | SND => fun x => SndSim  x
 | ELEM l => fun x => (PHI G l (coerce x))  
 end.

(*** Schema mappings ****************************************** *)

Record apgMapping S T := newapgMapping {
  oMap : L0 S -> Ty (L0 T);
  aMap : forall (l:L0 S), 
   @term (L0 T) (SIGMA T) (oMap l) (MapTy oMap (SIGMA S l))
}.

Definition apgMtoF0 {S T a b} (F: apgMapping S T) :
@term (L0 S) (SIGMA S) a b ->
@term (L0 T) (SIGMA T) (MapTy (oMap F) a) (MapTy (oMap F) b).
intros t; induction t; try constructor; auto.
 destruct F; simpl in *; auto.
 apply (COMP IHt1 IHt2).
Defined.

Lemma apgMtoFProper {S T} (F: apgMapping S T) {a b : Ty (L0 S)} (t1 t2: term a b):
 termEq t1 t2 -> termEq (apgMtoF0 F t1) (apgMtoF0 F t2).
Proof.
 intros.
 induction H. constructor. constructor; auto.
 apply (termTrans IHtermEq1 IHtermEq2).
 apply (termCongComp IHtermEq1 IHtermEq2).
 apply (termCongPair IHtermEq1 IHtermEq2).
 apply (termCongCase IHtermEq1 IHtermEq2).
 apply (termId1). apply termId2. apply termAssoc.
 apply termOne. apply termZero. 
 apply termTimesBeta1. apply termTimesBeta2.
 apply termPlusBeta1. apply termPlusBeta2. 
 apply termTimesEta. apply termPlusEta.
Qed.

Lemma apgMtoFProper0 {S T} (F: apgMapping S T) {a b : Ty (L0 S)} (t1 t2: term a b):
 termEq t1 t2 -> termEqc (apgMtoF0 F t1) = termEqc (apgMtoF0 F t2).
Proof.
 intros. apply pfResp1. apply apgMtoFProper. auto.
Defined.

Definition apgMtoFHelper {S T} (F : apgMapping S T) (x y : Ty (L0 S)) :
 forall t : term x y, termEq (apgMtoF0 F t)(termRepr 
 (@pfMake  _ _ termEquiv axiomQ _
 (fun t1 : term x y => eqc axiomQ (apgMtoF0 F t1))
 (apgMtoFProper0 F) (eqc axiomQ t))).
Proof.
 intros. apply (@pfResp2 _ _ _ (@axiomQ _ _ termEquiv)).
 unfold termRepr. rewrite @pfSurj. symmetry.
 rewrite pfProp. apply pfResp1. 
 apply apgMtoFProper.
 apply (@pfResp2 _ _ _ (@axiomQ _ _ termEquiv ) ). auto.
Defined.

(* Lemma 2: Each schema mapping induces a functor. *)

Definition apgMtoF {S T} (F: apgMapping S T)
 : Functor (@freeBCC (L0 S) (SIGMA S)) (@freeBCC (L0 T) (SIGMA T)).
simple refine (newFunctor (@freeBCC (L0 S) (SIGMA S)) (@freeBCC (L0 T) (SIGMA T)) 
(fun o => MapTy (oMap F) o) (fun a b  => _) _ _). simpl in *.

 apply (@mapQ _ _ _ _ termEquiv termEquiv axiomQ axiomQ (@apgMtoF0 S T  a b F) (@apgMtoFProper S T F a b)).

 intros. unfold mapQ. simpl in *. 
 pose (pfProp (@axiomQ _ _ (@termEquiv (L0 S) (SIGMA S) x x))
 (fun t1 : term x x => termEqc (apgMtoF0 F t1)) (apgMtoFProper0 F) IDEN).
 simpl in *. rewrite <- e. f_equal.

 intros. unfold mapQ. simpl in *.
 pose (pfProp 
  (@axiomQ _ _ 
     (@termEquiv (L0 S) (SIGMA S) x z))
  (fun t1 : @term (L0 S) (SIGMA S) x z =>
   termEqc (@apgMtoF0 S T x z F t1))
  ((fun (x0 y0 : term x z) (pf0 : termEq x0 y0) =>
   pfResp1 axiomQ (apgMtoFProper F pf0))) (COMP (termRepr f) (termRepr g))).
 clearbody e. simpl in *.
 unfold termEqc in *. unfold termRepr in *. 
 rewrite e. 
 apply   (@pfResp1 _ _ _ (@axiomQ _ _ termEquiv)).
 apply termCongComp. 

 clear e g z.
 pose (pfProp 
  (@axiomQ _ _ 
     (@termEquiv (L0 S) (SIGMA S) x y))
  (fun x0 : term x y => eqc (@axiomQ _ _ termEquiv) (apgMtoF0 F x0))
        (fun (x0 y0 : term x y) (pf0 : termEq x0 y0) =>
         pfResp1 (@axiomQ _ _ termEquiv) (apgMtoFProper F pf0))
 (termRepr f)). simpl in e.
 apply   (@pfResp2 _ _ _ (@axiomQ _ _ termEquiv)).
 unfold termRepr in *. simpl in *.
 rewrite <- e. rewrite pfSurj. rewrite pfSurj.
 f_equal.

 clear e f x. rename g into f. 
 rename y into x. rename z into y.
 pose (pfProp 
  (@axiomQ _ _ 
     (@termEquiv (L0 S) (SIGMA S) x y))
  (fun x0 : term x y => eqc (@axiomQ _ _ termEquiv) (apgMtoF0 F x0))
        (fun (x0 y0 : term x y) (pf0 : termEq x0 y0) =>
         pfResp1 (@axiomQ _ _ termEquiv) (apgMtoFProper F pf0))
(termRepr f)). simpl in e.
 apply   (@pfResp2 _ _ _ (@axiomQ _ _ termEquiv)).
 unfold termRepr in *. simpl in *.
 rewrite <- e. rewrite pfSurj. rewrite pfSurj.
 f_equal.
Defined.

Record IsBC {S} (G : Functor (freeBCC (SIGMA S)) SET) := newIsBC {
 IsBCZero :  ApplyO G (Zero _) = Empty_set;
 IsBCOne : ApplyO G (One _) = unit;
 IsBCPlus : forall {t1 t2}, ApplyO G (Plus t1 t2) = ApplyO G t1 + ApplyO G t2;
 IsBCTimes : forall {t1 t2}, ApplyO G (Times t1 t2) = ApplyO G t1 * ApplyO G t2;
 IsBCBaseApplyO : forall {b}, ApplyO G (Base _ b) = P b
}.

Definition functorToAPG {S} (G: Functor (freeBCC (SIGMA S)) SET)
 (pfBc : IsBC G) : apg S. 
refine (@newapg S (fun l => applyO G (Label l))
 (fun l e =>  _ )). simpl in *.
 pose ( @applyF _ _ G _ _ (termEqc (@ELEM _ (SIGMA S) l)) e).
 unfold applyO in *. unfold applyF in *.
 clearbody a. destruct pfBc. induction (SIGMA S l).
 rewrite IsBCZero0 in a. elim a.
 constructor.
 rewrite IsBCPlus0 in a. destruct a.
 apply Inl0. apply IHt1. auto.
 apply Inr0. apply IHt2. auto.
 rewrite IsBCTimes0 in a. exact (Pair0 (IHt1 (fst a)) (IHt2 (snd a))). 
 rewrite IsBCBaseApplyO0 in a. constructor. auto.
 constructor. auto.
Defined.

(* Theorem 1: The functor induced by an APG is bi-cartesian. *)

Lemma apgIsBc {S} (g: apg S) : IsBC (apgToFunctor g).
Proof. 
 apply newIsBC; simpl; auto.
Qed.

Record IsBC2 {S T} (G : Functor (freeBCC (SIGMA S)) (freeBCC (SIGMA T)))
 := newIsBC2 {
 IsBCZero2 :  ApplyO G (Zero _) = Zero _;
 IsBCOne2 : ApplyO G (One _) = One _;
 IsBCPlus2 : forall {t1 t2}, ApplyO G (Plus t1 t2) = Plus (ApplyO G t1) (ApplyO G t2);
 IsBCTimes2 : forall {t1 t2}, ApplyO G (Times t1 t2) = Times (ApplyO G t1) (ApplyO G t2);
 IsBCBaseApplyO2 : forall {b}, ApplyO G (Base _ b) = Base _ b
}.

Definition apgFtoM {S T} (G: Functor (@freeBCC (L0 S) (SIGMA S)) (@freeBCC (L0 T) (SIGMA T)))
 (pfBC: IsBC2 G) : apgMapping S T.
refine (@newapgMapping S T (fun l => applyO G (Label l))
 (fun l => _)).
pose (applyF G (termEqc (ELEM l))) as a.
 unfold applyO in *. unfold applyF in *.
 clearbody a. simpl in *. apply termRepr in a. simpl in *.
 refine (COMP a _). clear a.
 induction (SIGMA S l); simpl in *; intros.
 rewrite IsBCZero2; auto. apply IDEN. apply tT. 
 pose (CASE (COMP IHt1 INL) (COMP IHt2 INR)). 
 rewrite IsBCPlus2 . auto. auto.
 rewrite IsBCTimes2. refine (PAIR (COMP FST IHt1) (COMP SND IHt2)). auto.
 rewrite IsBCBaseApplyO2. constructor; auto. auto.
 constructor; auto.
Defined.

(* Lemma 2: The functor induced by a schema mapping is bi-cartesian. *)

Lemma apgMappingIsBc {S T} (F: apgMapping S T) : IsBC2 (apgMtoF F).
Proof. 
 apply newIsBC2; simpl; auto.
Qed.

End APG. 



