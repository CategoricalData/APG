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

(* Algebraic Property Graphs  ******************************************)

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

Inductive Term {E L} (lam : E -> L) : Ty L -> Type :=
 | ID  : forall e, Term lam (Label  (lam e))
 | Prim: forall b (c: P b), Term lam (Base _ b)
 | Tt  : Term lam (One _)
 | Pair: forall {t t'}, Term lam t -> Term lam t' -> Term lam (Times t t')
 | Inl : forall {t t'}, Term lam t -> Term lam (Plus  t t')
 | Inr : forall {t t'}, Term lam t'-> Term lam (Plus  t t').

Fixpoint MapTy {L1 L2} (f: L1 -> @Ty L2) (ty: @Ty L1) : @Ty L2 := 
 match ty with
  | Zero  _     => Zero  _
  | One   _     => One   _
  | Plus  a b => Plus  (MapTy f a) (MapTy f b)
  | Times a b => Times (MapTy f a) (MapTy f b)
  | Label l   => f l
  | Base  _ b   => Base  _ b
 end.

Fixpoint MapTerm {E1 L1} {lam1 : E1 -> L1} {E2 L2} {lam2 : E2 -> L2} 
  (g : L1 -> Ty L2) (h : forall (e:E1), Term lam2 (g (lam1 e))) 
      {ty} (term: Term lam1 ty) : Term  lam2 (MapTy g ty) :=
  match term with
 | ID   _ e   =>  h e
 | Prim _ c =>  Prim lam2 c
 | Tt   _     =>  Tt _
 | Pair  x y =>  Pair  (MapTerm g h x) (MapTerm g h y)
 | Inl   x   =>  Inl   (MapTerm g h x)
 | Inr   y   =>  Inr   (MapTerm g h y)
end.

Definition mapTy {L1 L2} (f: L1 -> L2) (ty: @Ty L1) : @Ty L2
  := MapTy (fun x => Label (f x)) ty.

Definition mapTerm {E1 L1} {lam1 : E1 -> L1} {E2 L2} {lam2 : E2 -> L2} 
  (f : L1 -> L2) (g : E1 -> E2) (pfNat : forall e, f (lam1 e) = lam2 (g e))
      : forall {ty} (x:Term lam1 ty) , Term  lam2 (mapTy f ty).
refine (fix mapTerm  {ty} term := match term with
 | ID   _ e   =>  _
 | Prim _ c =>  Prim lam2 c
 | Tt   _     =>  Tt _
 | Pair x y =>  Pair  (mapTerm x) (mapTerm y)
 | Inl  x   =>  Inl   (mapTerm x)
 | Inr  y   =>  Inr   (mapTerm y)
end). simpl. pose (ID lam2 (g e)). rewrite <- (pfNat e) in t. exact t.
Defined.

Record APG := newAPG {
 L : Type;
 sigma : L -> Ty L;
 E   : Type;
 lam : E -> L;
 phi : forall e, Term lam (sigma (lam e));
}.

(* Morphisms of APGs **********************************************)

Record APGMorphism (G1 G2: APG) := newAPGMorphism {
  lMap : L G1 -> L G2 ;
  eMap : E G1 -> E G2 ;
  pfNat : forall e, lMap (lam G1 e) = lam G2 (eMap e);
}.

Lemma APGMorphismEq (G1 G2: APG) (h1 h2 : APGMorphism G1 G2)  : 
  lMap h1 = lMap h2 -> eMap h1 = eMap h2 -> h1 = h2.
Proof.
 intros pf1 pf2. destruct h1,h2; simpl in *. subst. f_equal. apply proof_irrelevance.
Qed.

Definition TransHelper1  G H (j k:APGMorphism G H) e0 : eMap  j e0 =
              eMap  k e0 ->  lMap  j (lam G e0) =
 lMap  k (lam G e0).
 intros pf. rewrite  (pfNat j e0) . rewrite  (pfNat k e0) .
 rewrite pf. auto.
Defined.

Definition IdApgMorphism G : APGMorphism G G.
refine (newAPGMorphism G G (fun l => l) (fun e => e) (fun e => refl_equal _)).
Defined.

Definition ApgMorphismCompose {G1 G2 G3} (F: APGMorphism G1 G2) (G: APGMorphism G2 G3) : APGMorphism G1 G3.
refine (newAPGMorphism G1 G3 (fun l => lMap  G (lMap  F l)) (fun e => eMap  G (eMap  F e)) _).
intros e. destruct F,G. simpl. rewrite pfNat0. rewrite pfNat1. reflexivity.
Defined.

Definition APGInst : Category. 
refine (@newCategory APG APGMorphism IdApgMorphism (@ApgMorphismCompose) _ _ _).
intros. unfold IdApgMorphism,ApgMorphismCompose. destruct f. simpl. f_equal. apply proof_irrelevance.
intros. unfold IdApgMorphism,ApgMorphismCompose. destruct f. simpl. f_equal. apply proof_irrelevance.
intros. unfold IdApgMorphism,ApgMorphismCompose. destruct f,g,h. simpl in *. f_equal. apply proof_irrelevance.
Defined.

Lemma lemma1 {X Y}
(f g : Hom Y X)
(Q0 : ob APGInst)
(q0 : Hom Q0 Y)
(pf : comp q0 f = comp q0 g)
(l : L Q0)
(pfNq : lMap  f (lMap  q0 l) <>
       lMap  g (lMap  q0 l)) : False.
Proof.
 destruct f,g; simpl in *. unfold ApgMorphismCompose in *. simpl in *.
 inversion pf. pose (FnHelper l H0). contradiction.
Qed.

Lemma lemma2 {X Y}
(f g : Hom Y X)
(Q0 : ob APGInst)
(q0 : Hom Q0 Y)
(pf : comp q0 f = comp q0 g)
(e : E Q0)
(pfNq : eMap  f (eMap  q0 e) <>
       eMap  g (eMap  q0 e)) : False.
Proof.
 destruct f,g; simpl in *. unfold ApgMorphismCompose in *. simpl in *.
 inversion pf. pose (FnHelper e H1). contradiction.
Qed.

(* Constructions on APGs ******************************************)

Definition InitialAPG : APG := @newAPG Empty_set (fun x => match x with end) 
  Empty_set (fun x => match x with end) (fun x => match x with end).
Definition InitialAPGMorphism (G: APG) : APGMorphism InitialAPG G.
refine (newAPGMorphism InitialAPG G 
  (fun x => match x with end) (fun x => match x with end) _).
intros. elim e.
Defined.

Theorem APGInstInitial : @initial APGInst InitialAPG.
Proof.
  intros a. exists (InitialAPGMorphism a). 
  split; auto. intros. apply APGMorphismEq. 
  apply functional_extensionality_dep. intros x; elim x.
  apply functional_extensionality_dep. intros x; elim x.
Qed.
 
Definition TerminalAPG : APG := @newAPG unit (fun x => One _) 
  unit (fun x => tt) (fun x => Tt _).
Definition TerminalAPGMorphism (G: APG) : APGMorphism G TerminalAPG.
refine (newAPGMorphism G TerminalAPG (fun x => tt) (fun x => tt) _).
intros. auto.
Defined.

Theorem APGInstTerminal : @terminal APGInst TerminalAPG.
Proof.
  intros a. exists (TerminalAPGMorphism a). 
  split; auto. intros h. intros pf; clear pf. apply APGMorphismEq. 
  apply functional_extensionality_dep. intros l.
  unfold TerminalAPG,TerminalAPGMorphism;simpl.
  match goal with [ _ : _ |- tt = ?x ] => destruct x end. auto.
  unfold TerminalAPG,TerminalAPGMorphism;simpl.
  apply functional_extensionality_dep. intros e. 
  match goal with [ _ : _ |- tt = ?x ] => destruct x end. auto.
Qed.

Definition CoProductAPG (G1 G2 : APG) : APG.
refine (@newAPG 
  (L G1 + L G2)
  (fun l => match l with 
   | inl a => mapTy inl (sigma G1 a)
   | inr b => mapTy inr (sigma G2 b)
   end)
  (E G1 + E G2) 
  (fun l => match l with 
   | inl a => inl (lam G1 a)
   | inr b => inr (lam G2 b)
   end)
  (fun e => match e with 
   | inl a => mapTerm inl inl _ (phi G1 a)
   | inr b => mapTerm inr inr _ (phi G2 b)
   end)); auto. 
Defined.

Definition InlAPGMorphism (G1 G2: APG) 
  : APGMorphism G1 (CoProductAPG G1 G2).
refine (newAPGMorphism G1 (CoProductAPG G1 G2) (inl) (inl) _).
intros. auto.
Defined.

Definition InrAPGMorphism (G1 G2: APG) 
  : APGMorphism G2 (CoProductAPG G1 G2).
refine (newAPGMorphism G2 (CoProductAPG G1 G2) (inr) (inr) _).
intros. auto.
Defined.

Definition APGCoproduct (X1 X2:  APG)
  Y (f1 : APGMorphism X1 Y) (f2 : APGMorphism X2 Y)
: APGMorphism (CoProductAPG X1 X2) Y. 
refine (newAPGMorphism (CoProductAPG X1 X2) Y  (fun l => match l with 
   | inl a =>  lMap  f1 a
   | inr b =>  lMap  f2 b
   end) (fun e => match e with 
   | inl a =>  eMap  f1 a
   | inr b =>  eMap  f2 b
   end) _). intros. destruct e; simpl. destruct f1. auto. destruct f2. auto.
Defined.

Theorem APGHasCoProducts {X1 X2} : @coproduct APGInst X1 X2 (CoProductAPG X1 X2) (InlAPGMorphism X1 X2) (InrAPGMorphism X1 X2).
 intros X. intros. exists (@APGCoproduct X1 X2 X f1 f2).
 split. split. 
 apply APGMorphismEq. auto. auto.
 apply APGMorphismEq. auto. auto.
 intros f pf. destruct pf as [pf1 pf2]. 
 subst. simpl. destruct f,X1,X2,X; compute in *.
 apply APGMorphismEq. simpl in *.  apply functional_extensionality_dep.  intros x; destruct x; auto.
 simpl in *.  apply functional_extensionality_dep.  intros x; destruct x; auto.
Qed.

Definition ProductAPG (G1 G2 : APG) : APG.
refine (@newAPG 
  (L G1 * L G2)
  (fun l => match l with 
   | (a, b) => Times (mapTy (fun x => (x, b)) (sigma G1 a))
                       (mapTy (fun x => (a, x)) (sigma G2 b))
   end)
  (E G1 * E G2) 
  (fun l => match l with 
   | (a, b) => (lam G1 a, lam G2 b)
   end)
  (fun e => match e with 
   | (a, b) => Pair  
                (mapTerm _ (fun x => (x, b)) _ (phi G1 a))
                (mapTerm _ (fun x => (a, x)) _ (phi G2 b))
   end)); auto.
Defined.

Definition FstAPGMorphism (G1 G2: APG) 
  : APGMorphism (ProductAPG G1 G2) G1.
refine (newAPGMorphism (ProductAPG G1 G2) G1 fst fst _).
intros. destruct e. compute. auto.
Defined.

Definition SndAPGMorphism (G1 G2: APG) 
  : APGMorphism (ProductAPG G1 G2) G2.
refine (newAPGMorphism (ProductAPG G1 G2) G2 snd snd _).
intros. destruct e. compute. auto.
Defined.

Definition APGProduct (X1 X2:  APG)
  Y (f1 : APGMorphism Y X1) (f2 : APGMorphism Y X2)
: APGMorphism Y (ProductAPG X1 X2). 
refine (newAPGMorphism Y (ProductAPG X1 X2) 
 (fun l => (lMap  f1 l, lMap  f2 l)) 
 (fun e => (eMap  f1 e, eMap  f2 e))
 _). intros. simpl. f_equal. destruct f1.  simpl. auto.
 destruct f2. simpl. auto.
Defined.

Theorem APGHasProducts {X1 X2} : @product APGInst X1 X2 (ProductAPG X1 X2) (FstAPGMorphism X1 X2) (SndAPGMorphism X1 X2).
Proof.
 intros X. intros. exists (@APGProduct X1 X2 X f1 f2).
 split. split. 
 apply APGMorphismEq. auto. auto.
 apply APGMorphismEq. auto. auto.
 intros f pf. destruct pf as [pf1 pf2]. 
 subst. simpl. destruct f,X1,X2,X; compute in *.
 apply APGMorphismEq. simpl in *.  apply functional_extensionality_dep.
 intros x. destruct (lMap0 x). auto.
 simpl in *. apply functional_extensionality_dep. intros x.
 destruct (eMap0 x); auto.
Qed.

Definition EqualizerAPG {G H : APG} (j k : APGMorphism G H) : APG.
refine (@newAPG 
  { l : L G | lMap  j l = lMap  k l }
  (fun l => match l with 
   | exist _ l0 pf => MapTy (fun l1 => 
    match EqDecAx (lMap  j l1) (lMap k l1) with
     | left  pfEq => Plus (One _) (Label (exist _ l1 pfEq))
     | right pfEq => One _
    end) (sigma G l0)   
  end)
  { e : E G | eMap j e = eMap k e }
  (fun e => match e with 
   | exist _ e0 pf => exist _ (lam G e0) (TransHelper1 j k e0 pf)
  end)
  (fun e => match e with 
   | exist _ e0 pf => MapTerm (fun l1 => 
    match EqDecAx (lMap  j l1) (lMap  k l1) with
     | left  pfEq => Plus (One _) (Label (exist _ l1 pfEq))
     | right pfEq => One _
    end)
    (fun e1 => match EqDecAx (eMap  j e1) (eMap  k e1) with
     | left  pfEq => _
     | right pfEq => _ end ) (phi G e0) 
  end)
).
pose (TransHelper1 j k e1 pfEq). 
   pose (ID (fun
     e2 : {e2 : E G |
          eMap j e2 = eMap k e2}
   =>
   let (e3, pf0) := e2 in
   exist
     (fun l : L G =>
      lMap j l = lMap k l)
     (lam G e3)
     (TransHelper1 j k e3 pf0)) (exist _ e1 pfEq)).
destruct ( EqDecAx (lMap  j (lam G e1))
      (lMap  k (lam G e1)) ).
assert ((TransHelper1 j k e1 pfEq) = e3). apply proof_irrelevance. rewrite <- H0. exact (Inr  t).
contradiction. 
destruct ( EqDecAx (lMap  j (lam G e1))
      (lMap  k (lam G e1)) ). apply Inl. apply Tt. apply Tt.
Defined.

Definition EqualizerAPGMorphism {G H : APG} (j k : APGMorphism G H) 
 : APGMorphism (EqualizerAPG j k) G.
refine (newAPGMorphism (EqualizerAPG j k) G 
 (fun l => proj1_sig l) (fun e => proj1_sig e) _).
intros. destruct e. simpl in *. auto.
Defined.

Definition ApgEqualizerHelper {X Y}  (f g : Hom Y X) 
 (Q0 : ob APGInst) (q0 : Hom Q0 Y) (pf : comp q0 f = comp q0 g)
 : Hom Q0 (EqualizerAPG f g).
refine (newAPGMorphism Q0 (EqualizerAPG f g)
  (fun l => match EqDecAx (lMap  f (lMap  q0 l)) (lMap g (lMap  q0 l)) with
    | left  pfEq => exist _ (lMap  q0 l) pfEq
    | right pfNq => match lemma1    pf l pfNq with end
   end) (fun e => match EqDecAx (eMap  f (eMap  q0 e)) (eMap g (eMap  q0 e)) with
    | left  pfEq => exist _ (eMap  q0 e) pfEq
    | right pfNq => match lemma2 pf e pfNq with end
   end) _).
 intros. destruct f,g; simpl in *.
 unfold ApgMorphismCompose in *. simpl in *.
 inversion pf. simpl in *.
 destruct X,Y,q0,Q0; compute in *.
 pose (FnHelper e H1). pose (FnHelper (lam2 e) H0).
 simpl in *. destruct ( EqDecAx (lMap0 (lMap2 (lam2 e)))
    (lMap1 (lMap2 (lam2 e))) ). simpl in *.
 apply ExPfIrr. simpl. destruct (EqDecAx (eMap0 (eMap2 e))
         (eMap1 (eMap2 e))). simpl.  auto. 
 simpl. contradiction. simpl. contradiction.
Defined.

Theorem APGHasEqualizers {X Y} f g : @equalizer APGInst X Y f g 
 (EqualizerAPG f g) (EqualizerAPGMorphism f g).
Proof.
 split. simpl. unfold EqualizerAPGMorphism,ApgMorphismCompose. 
  apply APGMorphismEq. simpl. apply functional_extensionality.
  intros l0; destruct l0; simpl in *; auto.
  simpl. apply functional_extensionality.
  intros l0; destruct l0; simpl in *; auto.
  intros Q0 q0 pf. exists (ApgEqualizerHelper   pf).
  destruct f,g. unfold ApgMorphismCompose in *.
  unfold comp in *. unfold Comp in *. simpl in *. inversion pf. split. 
  apply APGMorphismEq. simpl. apply functional_extensionality.
  intros l. pose (FnHelper l H0).
 simpl in *. destruct (  EqDecAx (lMap0 (lMap  q0 l))
      (lMap1 (lMap q0 l)) ). simpl in *. auto.
 contradiction. simpl in *. 
 apply functional_extensionality. 
 intros e. pose (FnHelper e H1). destruct (  EqDecAx (eMap0 (eMap  q0 e))
      (eMap1 (eMap  q0 e)) ). simpl in *. auto.
 simpl in *. contradiction. 
 intros u pf2. apply APGMorphismEq. simpl. apply functional_extensionality.
  intros l. pose (FnHelper l H0).
 simpl in *. destruct (  EqDecAx (lMap0 (lMap  q0 l))
      (lMap1 (lMap  q0 l)) ). apply ExPfIrr. simpl.
 subst. simpl in *. auto. contradiction.
 simpl in *. apply functional_extensionality. 
 intros e. pose (FnHelper e H1). destruct (  EqDecAx (eMap0 (eMap  q0 e))
      (eMap1 (eMap  q0 e)) ). simpl in *. apply ExPfIrr. simpl in *.
 subst. simpl in *. auto. contradiction.
Qed.

(*******************************************************************)
(* For co-equalizers, we specialize the definitions.               *)

Section coeq.

Variable sL : Type.
Variable ssigma : sL -> Ty sL.

Record sAPG := newsAPG {
 sE   : Type;
 slam : sE -> sL;
 sphi : forall e, Term slam (ssigma (slam e));
}.

Record sAPGMorphism (G1 G2: sAPG) := newsAPGMorphism {
  seMap : sE G1 -> sE G2 ;
  spfNat : forall e,  (slam G1 e) = slam G2 (seMap e)
}.

Lemma sAPGMorphismEq (G1 G2: sAPG) (h1 h2 : sAPGMorphism G1 G2)  : 
  seMap h1 = seMap h2 -> h1 = h2.
Proof.
 intros pf1. destruct h1,h2; simpl in *. subst. f_equal. apply proof_irrelevance.
Qed.

Definition IdsApgMorphism G : sAPGMorphism G G.
refine (newsAPGMorphism G G (fun e => e) (fun e => refl_equal _)).
Defined.

Definition sApgMorphismCompose {G1 G2 G3} (F: sAPGMorphism G1 G2) (G: sAPGMorphism G2 G3) : sAPGMorphism G1 G3.
refine (newsAPGMorphism G1 G3 (fun e => seMap  G (seMap  F e)) _).
intros e. destruct F,G. simpl. rewrite spfNat0. rewrite spfNat1. reflexivity.
Defined.

Definition sAPGInst : Category. 
refine (@newCategory sAPG sAPGMorphism IdsApgMorphism (@sApgMorphismCompose) _ _ _).
intros. unfold IdsApgMorphism,sApgMorphismCompose. destruct f. simpl. f_equal. apply proof_irrelevance.
intros. unfold IdsApgMorphism,sApgMorphismCompose. destruct f. simpl. f_equal. apply proof_irrelevance.
intros. unfold IdsApgMorphism,sApgMorphismCompose. destruct f,g,h. simpl in *. f_equal. apply proof_irrelevance.
Defined.

Definition mapTermAlt {E1} {lam1 : E1 -> sL} {E2}   
   (g : E1 -> E2) : forall
       {ty} (x:Term lam1 ty) (lam2 : E2 -> sL) 
  (pfNat : forall e,  (lam1 e) = lam2 (g e)) , Term lam2 ty.
refine (fix mapTermAlt  {ty} term lam2 pf := match term with
 | ID   _ e   =>  _
 | Prim _ c =>  Prim  _ c
 | Tt   _     =>  Tt _
 | Pair x y =>  Pair  (mapTermAlt x lam2 pf) (mapTermAlt y lam2 pf)
 | Inl  x   =>  Inl   (mapTermAlt x lam2 pf)
 | Inr  y   =>  Inr   (mapTermAlt y lam2 pf)
end). simpl. pose (ID lam2 (g e)). rewrite <- (pf e) in t. exact t.
Defined.

Definition CoEqualizersAPG {G1 G2} (j k : sAPGMorphism G1 G2) 
(pf: forall x y, Lift (seMap  j) (seMap  k) x y -> slam G2 x = slam G2 y) : sAPG.

refine (@newsAPG (quotient (seMap  j) (seMap  k)) 
 (fun e => slam G2 (Repr _ _ e)) (fun e => _ (sphi G2 (Repr _ _ e)))).
intros a.
apply (@mapTermAlt (sE G2) (slam G2) (quotient (seMap  j) (seMap k)) (fun x => Eqc _ _ x) (ssigma (slam G2 (Repr _ _ e))) a (fun e => slam G2 (Repr _ _ e))).
intros x. apply pf. unfold Repr,Eqc,quotient in *.
 destruct ( (axiomQ 
           )). simpl in *.  apply pfResp4. auto.
Defined.

Definition CoEqualizersAPGMorphism {G1 G2} (j k : sAPGMorphism G1 G2) 
(pf: forall x y, Lift (seMap j) (seMap  k) x y -> slam G2 x = slam G2 y) 
: sAPGMorphism G2 (CoEqualizersAPG j k pf).
destruct j,k,G2. refine (newsAPGMorphism _ (CoEqualizersAPG
     {|
     seMap := seMap0;
     spfNat := spfNat0 |}
     {|
     seMap := seMap1;
     spfNat := spfNat1 |} pf) (fun e => Eqc _ _ e) _).
 compute in *.
destruct ( (axiomQ )). simpl in *.
intros e. apply pf. auto.
Defined.

Definition ApgCoEqualizerHelper 
  {G1 G2}
  (j k : sAPGMorphism G1 G2)
  (pf : forall x y : sE G2,
      Lift (seMap  j)
        (seMap  k) x y ->
      slam G2 x = slam G2 y)
  {Q0}
  (q0 : sAPGMorphism G2 Q0)
  (H : sApgMorphismCompose j q0 =
    sApgMorphismCompose k q0)
 : hom sAPGInst (CoEqualizersAPG j k pf) Q0.
refine (newsAPGMorphism (CoEqualizersAPG j k pf) Q0 (fun e => seMap  q0 (Repr _ _ e)) _).
 destruct j,k,q0,Q0. compute in *. destruct ( (axiomQ  )). 
  intros q.  apply spfNat2.
Defined.

Theorem APGHasCoEqualizers {G1 G2} 
(j k : sAPGMorphism G1  G2)
 (pf3: forall x y, Lift (seMap j) (seMap  k) x y -> slam G2 x = slam G2 y)
: @coequalizer sAPGInst _ _ j k
 (CoEqualizersAPG j k pf3) (CoEqualizersAPGMorphism j k pf3).
Proof.
  split.  
  apply sAPGMorphismEq. apply functional_extensionality. intros e.
  destruct j,k,G1,G2. compute in *. 
  destruct ( (axiomQ )). 
  apply pfResp3. apply LiftInj.

  simpl in *. intros. exists (@ApgCoEqualizerHelper G1 G2  j k pf3 Q0 q0 H). split.
  destruct j,k,q0,Q0,G1,G2. compute in *.
  destruct ( (axiomQ )).  
  compute in *. apply sAPGMorphismEq. simpl in *.
  inversion H; clear H. apply functional_extensionality_dep. intros e.
  induction (pfResp4 e (repr0 (eqc0 e))). auto. auto. congruence. symmetry. apply (FnHelper s H1). auto.

  intros u pf. destruct j,k,q0,Q0,G1,G2,u. compute in *.
  destruct ( (axiomQ )).  
  inversion H; clear H. 
  inversion pf; clear pf. subst.
  apply sAPGMorphismEq. simpl in *.
  apply functional_extensionality_dep. intros q.
  rewrite (pfSurj0 q). auto.
Qed.

End coeq.

(* The Commutative Square Category ********************************* *)

Inductive  CD_O : Type := EE | TT | LL | VV.
Inductive  CD_A : CD_O -> CD_O -> Type := | EEEE : CD_A EE EE | EEVV : CD_A EE VV | TTTT : CD_A TT TT | LLLL : CD_A LL LL | VVVV : CD_A VV VV | EELL : CD_A EE LL | LLTT : CD_A LL TT | VVTT : CD_A VV TT | EETT : CD_A EE TT.
Definition CD_id x: CD_A x x := match x as x return CD_A x x with | EE => EEEE | TT => TTTT | LL => LLLL | VV => VVVV end.
 
Definition CD_o1 x : forall z y (f: CD_A x y) (g: CD_A y z), CD_A x z.
refine (match x as x return forall z y (f: CD_A x y) (g: CD_A y z), CD_A x z with
  | EE => fun z => match z as z return forall y (f: CD_A EE y) (g: CD_A y z), CD_A EE z with | EE => fun y f g => EEEE | TT => fun y f g => EETT | LL => fun y f g => EELL | VV => fun y f g => EEVV end
  | TT => fun z => match z as z return forall y (f: CD_A TT y) (g: CD_A y z), CD_A TT z with | EE => fun y f g => _ | TT => fun y f g => TTTT | LL => fun y f g => _ | VV => fun y f g => _ end
  | LL => fun z => match z as z return forall y (f: CD_A LL y) (g: CD_A y z), CD_A LL z with | EE => fun y f g => _ | TT => fun y f g => LLTT | LL => fun y f g => LLLL | VV => fun y f g => _ end
  | VV => fun z => match z as z return forall y (f: CD_A VV y) (g: CD_A y z), CD_A VV z with | EE => fun y f g => _ | TT => fun y f g => VVTT | LL => fun y f g => _ | VV => fun y f g => VVVV end
 end); destruct y; inversion f; try auto; inversion g; try auto.
Defined.

Definition CD_o x y z (f: CD_A x y) (g: CD_A y z) : CD_A x z := CD_o1  f g.

Definition CDCat : Category. refine (@newCategory CD_O CD_A CD_id CD_o _ _ _); intros.
 destruct f; auto.
 destruct f; auto.
 inversion f; inversion g; inversion h;
 subst; try auto; try discriminate.
Defined.

Lemma lEEEE (g : CD_A EE EE) : g = EEEE. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lLLLL (g : CD_A LL LL) : g = LLLL. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lTTTT (g : CD_A TT TT) : g = TTTT. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lVVVV (g : CD_A VV VV) : g = VVVV. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lEELL (g : CD_A EE LL) : g = EELL. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lEETT (g : CD_A EE TT) : g = EETT. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lVVTT (g : CD_A VV TT) : g = VVTT. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lLLTT (g : CD_A LL TT) : g = LLTT. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lEEVV (g : CD_A EE VV) : g = EEVV. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lVVEE (g : CD_A VV EE) : False. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lVVLL (g : CD_A VV LL) : False. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lTTEE (g : CD_A TT EE) : False. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed. 
Lemma lTTLL (g : CD_A TT LL) : False. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lLLEE (g : CD_A LL EE) : False. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lTTVV (g : CD_A TT VV) : False. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.
Lemma lLLVV (g : CD_A LL VV) : False. Proof. refine (match g with | EEEE => _ | EEVV => _ | TTTT => _ | LLLL => _ | VVVV => _ | EELL => _ | LLTT => _ | VVTT => _ | EETT => _ end); compute; auto. Qed.

(* APG Morphisms as Natural Transformations *************************)

Definition APGtoFunctor (G:APG) : Functor CDCat SET. refine (
 newFunctor CDCat SET 
 (fun x => match x with
  | EE => E G
  | TT => Ty (L G)
  | LL => L G
  | VV => sigT (Term (lam G))
 end ) 
 (fun z y f => match f with
  | EEEE => fun x => x
  | TTTT => fun x => x
  | LLLL => fun x => x
  | VVVV => fun x => x
  | EEVV => fun x => existT _ _ (phi G x)
  | EELL => fun x => lam G x
  | LLTT => fun x => sigma G x
  | VVTT => fun x => projT1 x
  | EETT => fun x => sigma G (lam G x)
end) _ _).
 intros.  destruct x; auto. 
 intros.  destruct x,y,z;simpl;
 try (rewrite ( lEEEE g)); try (rewrite ( lLLLL g)); try (rewrite ( lTTTT g)); try (rewrite ( lVVVV g)); try (rewrite ( lEELL g)); try (rewrite ( lEETT g)); try (rewrite ( lVVTT g)); try (rewrite ( lLLTT g)); try (rewrite ( lEEVV g)); try (rewrite ( lVVEE g)); try (rewrite ( lVVLL g)); try (rewrite ( lTTEE g)); try (rewrite ( lTTLL g)); try (rewrite ( lLLEE g)); try (rewrite ( lTTVV g)); try (rewrite ( lLLVV g)); try (rewrite ( lEEEE f)); try (rewrite ( lLLLL f)); try (rewrite ( lTTTT f)); try (rewrite ( lVVVV f)); try (rewrite ( lEELL f)); try (rewrite ( lEETT f)); try (rewrite ( lVVTT f)); try (rewrite ( lLLTT f)); try (rewrite ( lEEVV f)); try (rewrite ( lVVEE f)); try (rewrite ( lVVLL f)); try (rewrite ( lTTEE f)); try (rewrite ( lTTLL f)); try (rewrite ( lLLEE f)); try (rewrite ( lTTVV f)); try (rewrite ( lLLVV f)) ; auto; 
 try (elim ( lEEEE g)); try (elim ( lLLLL g)); try (elim ( lTTTT g)); try (elim ( lVVVV g)); try (elim ( lEELL g)); try (elim ( lEETT g)); try (elim ( lVVTT g)); try (elim ( lLLTT g)); try (elim ( lEEVV g)); try (elim ( lVVEE g)); try (elim ( lVVLL g)); try (elim ( lTTEE g)); try (elim ( lTTLL g)); try (elim ( lLLEE g)); try (elim ( lTTVV g)); try (elim ( lLLVV g)); try (elim ( lEEEE f)); try (elim ( lLLLL f)); try (elim ( lTTTT f)); try (elim ( lVVVV f)); try (elim ( lEELL f)); try (elim ( lEETT f)); try (elim ( lVVTT f)); try (elim ( lLLTT f)); try (elim ( lEEVV f)); try (elim ( lVVEE f)); try (elim ( lVVLL f)); try (elim ( lTTEE f)); try (elim ( lTTLL f)); try (elim ( lLLEE f)); try (elim ( lTTVV f)); try (elim ( lLLVV f)).
Defined.

Definition APGInstBig : Category.
refine (
  @newCategory APG 
 (fun x y => Transform (APGtoFunctor x) (APGtoFunctor y) ) 
 (fun x => IdTrans (APGtoFunctor x) )
 (fun x y z f g => CompTrans f g ) _ _ _ ).
 intros; try apply TransPfIrr; try apply PI; simpl in *;
  apply functional_extensionality_dep ; intros;
 apply functional_extensionality_dep; intros; auto.
 intros; try apply TransPfIrr; try apply PI; simpl in *;
  apply functional_extensionality_dep ; intros;
 apply functional_extensionality_dep; intros; auto.
 intros; try apply TransPfIrr; try apply PI; simpl in *;
  apply functional_extensionality_dep ; intros;
 apply functional_extensionality_dep; intros; auto.
Defined.

(* Natural Transformations *************************************************)

Lemma ExistTHelper2 {A T} a t a0 t0 : 
 a = a0 -> (a = a0 -> JMeq t t0) -> @existT A T a t = @existT A T a0 t0.
Proof.
 intros pf. subst. intros pf. f_equal. pose (pf (refl_equal _)). 
 clearbody j. clear pf. auto. apply JMeq_eq. auto.
Qed.

Lemma TyInvOne {L E} {lam1 : E -> L} 
 (x : Term lam1 (One L)) : x = (Tt lam1).
Proof.
 refine (match x as x0 in Term _ z return z = One L -> JMeq x x0 -> x = Tt lam1 with
  | ID   _ e   =>  fun pf pf2 => _
  | Prim _ c =>  fun pf pf2 => _
  | Tt   _     =>  fun pf pf2 => _
  | Pair x y =>  fun pf pf2 => _
  | Inl  x   =>  fun pf pf2 => _
  | Inr  y   =>  fun pf pf2 => _
 end ( refl_equal _ ) (JMeq_refl _)); try discriminate; try auto.
 apply JMeq_eq. auto.
Qed.

Lemma TyInvZero {L E} {lam1 : E -> L} 
 (x : Term lam1 (Zero L)) : False.
Proof.
 refine (match x as x0 in Term _ z return z = Zero L -> JMeq x x0 -> False with
  | ID   _ e   =>  fun pf pf2 => _
  | Prim _ c =>  fun pf pf2 => _
  | Tt   _     =>  fun pf pf2 => _
  | Pair x y =>  fun pf pf2 => _
  | Inl   x   =>  fun pf pf2 => _
  | Inr   y   =>  fun pf pf2 => _
 end ( refl_equal _ ) (JMeq_refl _)); try discriminate; try auto.
Qed.

Lemma TyInvPair {L E} {lam1 : E -> L} {t1 t2} 
 (x : Term lam1 (Times t1 t2)) : exists a, exists b, 
    x = Pair a b.
Proof.
 refine (match x as x0 in Term _ z return z = Times  t1 t2 -> JMeq x x0 -> exists a, exists b, 
    x = Pair  a b with
  | ID   _ e   =>  fun pf pf2 => _
  | Prim _ c =>  fun pf pf2 => _
  | Tt   _     =>  fun pf pf2 => _
  | Pair  x y =>  fun pf pf2 => _
  | Inl   x   =>  fun pf pf2 => _
  | Inr   y   =>  fun pf pf2 => _
 end ( refl_equal _ ) (JMeq_refl _)); try discriminate; try auto.
assert (t0 = t2). injection pf. intros pf1. subst. auto.
subst. assert (t = t1). injection pf. auto. subst. clear pf.
exists x.  exists y. apply JMeq_eq. auto.
Qed.

Lemma TyInvPlus {L E} {lam1 : E -> L} {t1 t2} 
 (x : Term lam1 (Plus  t1 t2)) : (exists a, x = Inl  a ) \/ (exists b, x = Inr b).
Proof.
 refine (match x as x0 in Term _ z return z = Plus  t1 t2 -> JMeq x x0 -> 
    (exists a, x = Inl  a ) \/ (exists b, x = Inr  b) with
  | ID   _ e   =>  fun pf pf2 => _
  | Prim _  c =>  fun pf pf2 => _
  | Tt   _     =>  fun pf pf2 => _
  | Pair  x y =>  fun pf pf2 => _
  | Inl   x   =>  fun pf pf2 => _
  | Inr   y   =>  fun pf pf2 => _
 end ( refl_equal _ ) (JMeq_refl _)); try discriminate; try auto.
assert (t0 = t2). injection pf. intros pf1. subst. auto.
subst. assert (t = t1). injection pf. auto. subst. clear pf.
left. exists x. apply JMeq_eq. auto. right. assert (t0 = t2). injection pf. intros pf1. subst. auto.
subst. assert (t = t1). injection pf. auto. subst. clear pf.
exists y. apply JMeq_eq. auto. 
Qed.

Definition APGMorphismToTransform {G1 G2:APG} (h: APGMorphism G1 G2) 
  (pfNatL : forall l, sigma G2 (lMap  h l) = mapTy (lMap  h) (sigma G1 l)) 
  (pfNatE : forall e, mapTerm (lMap h) (eMap h) (pfNat h) (phi G1 e) = 
   match pfNatL (lam G1 e) in _ = y return Term (lam G2)
    y with
    | refl_equal => match symmetry (pfNat  h e) in _ = z 
       return Term (lam G2) (sigma G2 z) with
        | refl_equal => phi G2 (eMap  h e)
      end 
   end) : Transform (APGtoFunctor G1) (APGtoFunctor G2). 
refine (@newTransform CDCat SET (APGtoFunctor G1) (APGtoFunctor G2) 
 (fun x => match x with
  | EE => eMap  h
  | TT => mapTy (lMap h)
  | LL => lMap  h
  | VV => fun v => existT _ (mapTy (lMap  h) (projT1 v)) (mapTerm (lMap  h) (eMap  h) (pfNat h) (projT2 v) ) 
 end) _).
intros; 
  destruct G1,G2,h,f; simpl in *; auto.
Focus 2. apply functional_extensionality_dep. auto.
Focus 2. apply functional_extensionality_dep. intros w. rewrite (pfNatL w). auto.
Focus 2. apply functional_extensionality_dep. intros w. rewrite <- (pfNat0 w). auto.
apply functional_extensionality_dep. intros w. 
  rewrite  (pfNatE w). clear pfNatE. rewrite <- (pfNatL (lam0 w)).
  rewrite  (pfNat0 w). f_equal.
Qed.

Definition Gx1 : APG := @newAPG unit (fun x => Zero _) 
Empty_set (fun x => match x with end) (fun x => match x with end).
Definition Gx2 : APG := @newAPG unit (fun x => One _) 
Empty_set (fun x => match x with end) (fun x => match x with end).
Definition hx : APGMorphism Gx1 Gx2.
refine (newAPGMorphism Gx1 Gx2 (fun l => l) (fun e => match e with end) _).
intros. compute in *. elim e.
Defined.

Lemma ApgMorphismsNotNatural :  exists l,
   sigma Gx2 (lMap  hx l) <> mapTy (lMap  hx) (sigma Gx1 l). 
Proof.
 intros. exists tt. intros pf.
 simpl in *. unfold mapTy in pf. simpl in pf. discriminate.
Qed.

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
(* For migration, we specialize again *)

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
Qed.

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

End APG. 



