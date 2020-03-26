(* Monad comprehension calculus, by Ryan Wisnesky *********************************** *)

Require Import BinIntDef List Program.Equality.
Open Scope Z_scope.

Axiom functional_extensionality : forall {A B} (f g : A -> B),
  (forall x, f x = g x) -> f = g.

Axiom set_extensionality: forall {t} (P Q : t -> Prop), 
  (forall x, P x <-> Q x) -> P = Q.

Axiom decidable_equality: forall {T:Type} (a b : T), 
  {a = b} + {a <> b}.

Lemma equal_f : forall {A B : Type} {f g : A -> B},
  f = g -> forall x, f x = g x.
Proof.
  intros. case H. constructor. 
Defined.

Fixpoint foldr {A B G} (f:G*(unit+(A*B))->B) (g:G) (l: list A) : B :=
 match l with
  | nil => f (g, inl tt)
  | cons a b => f (g, inr (a, foldr f g b))
end.

Definition foldr0 {A B} (f:(unit+(A*B))->B) (l: list A) : B :=
 foldr (fun x => f (snd x)) tt l.

Fixpoint insertAt {A} t G n {struct n} : list A :=
 match n with
   | O => t :: G
   | S n' => match G with
               | nil => t :: G
               | t' :: G' => t' :: insertAt t G' n'
             end
 end.

Definition listToSet {t} (a : list t) (e:t) : Prop := In e a.

CoInductive Stream A := {shd : A; stl : Stream A}.

Arguments shd [A].
Arguments stl [A].

CoInductive EqSt {A} (s1 s2: Stream A) : Prop := {
  eqhd : shd s1 = shd s2; eqtl : EqSt (stl s1) (stl s2) }.

Arguments eqhd [A].
Arguments eqtl [A].

Axiom stream_extensionality: forall {t1} (s1 s2 : Stream t1), EqSt s1 s2 -> s1 = s2.

Definition Cons {A} (n:A) s := {| shd := n; stl := s |}.

CoFixpoint unfoldr0 {A B} (f:B->(A*B)) (l: B) : Stream A := 
  Cons (fst (f l)) (unfoldr0 f (snd (f l))). 

Definition unfoldr {A B G} (f:(G*B)->(A*B)) (g:G) (l: B) : Stream A :=
  @unfoldr0 A (G*B) (fun x => (fst (f x), (fst x, snd (f x)))) (g, l).

Section stream_eq_coind.
  Variable A : Type.
  Variable R : Stream A -> Stream A -> Prop.

  Hypothesis Cons_case_hd : forall {s1 s2}, R s1 s2 -> shd s1 = shd s2.
  Hypothesis Cons_case_tl : forall {s1 s2}, R s1 s2 -> R (stl s1) (stl s2).

  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> EqSt s1 s2.
    cofix o; destruct s1; destruct s2; intro.
    generalize (Cons_case_hd H); intro Heq; simpl in Heq; rewrite Heq.
    subst. constructor. simpl. auto.
    apply o. 
    apply (Cons_case_tl H).
  Qed.

End stream_eq_coind.

(* Structural (co-)recursion: Syntax and Semantics ****************************************** *)

Inductive Ty : Type :=
 | INT  : Ty
 | VOID : Ty
 | UNIT : Ty
 | PROD : Ty -> Ty -> Ty
 | SUM  : Ty -> Ty -> Ty
 | FN   : Ty -> Ty -> Ty
 | LIST   : Ty -> Ty
 | STREAM : Ty -> Ty
 | SET : Ty -> Ty.

Inductive Exp : Ty -> Ty -> Type :=
 | ID    : forall {t}, Exp t t
 | CONST : Z -> Exp UNIT INT
 | ADD : Exp (PROD INT INT) INT
 | MUL : Exp (PROD INT INT) INT
 | NEG : Exp INT INT
 | COMP  : forall {t1 t2 t3}, Exp t1 t2 -> Exp t2 t3 -> Exp t1 t3
 | INL   : forall {t1 t2}, Exp t1 (SUM t1 t2)
 | INR   : forall {t1 t2}, Exp t2 (SUM t1 t2)
 | PAIR  : forall {t1 t2 t3}, Exp t1 t2 -> Exp t1 t3 -> Exp t1 (PROD t2 t3)
 | FST   : forall {t1 t2}, Exp (PROD t1 t2) t1
 | SND   : forall {t1 t2}, Exp (PROD t1 t2) t2
 | TT    : forall {t}, Exp t UNIT
 | FF    : forall {t}, Exp VOID t
 | CASE  : forall {t1 t2 t3}, Exp t2 t1 -> Exp t3 t1 -> Exp (SUM t2 t3) t1
 | CURRY : forall {t1 t2 t3}, Exp (PROD t1 t2) t3 -> Exp t1 (FN t2 t3)
 | EVAL  : forall {t1 t2}, Exp (PROD (FN t1 t2) t1) t2
 | DIST  : forall {t1 t2 t3}, Exp (PROD t1 (SUM t2 t3)) (SUM (PROD t1 t2) (PROD t1 t3))
 | IN    : forall {t}, Exp ( (SUM UNIT (PROD t (LIST t)))) (LIST t)
 | OUT   : forall {t}, Exp ( (STREAM t)) (PROD t (STREAM t))
 | FOLD  : forall {t t' t''}, Exp (PROD t'' (SUM UNIT (PROD t t'))) t' -> Exp (PROD t'' (LIST t)) t'
 | UNFOLD: forall {t t'}, Exp t' (PROD t t') -> Exp t' (STREAM t)
 | MAP   : forall {t t'}, Exp t t' -> Exp (SET t) (SET t')
 | EMPTY : forall {t}, Exp UNIT (SET t)
 | SNG   : forall {t}, Exp t (SET t)
 | UNION : forall {t}, Exp (PROD (SET t) (SET t)) (SET t)
 | FLATTEN:forall {t}, Exp (SET (SET t)) (SET t)
 | TENSOR: forall {t t'}, Exp (PROD t (SET t')) (SET (PROD t t'))
 | EQ    : forall {t}, Exp (PROD t t) (SUM UNIT UNIT).

Fixpoint TyD t : Type := match t with
 | INT  => Z
 | VOID => Empty_set
 | UNIT => unit
 | PROD t1 t2 => TyD t1 * TyD t2
 | SUM  t1 t2 => TyD t1 + TyD t2
 | FN   t1 t2 => TyD t1 -> TyD t2
 | LIST   t => list (TyD t)
 | SET    t => TyD t -> Prop
 | STREAM t => Stream (TyD t)
end.

Fixpoint ExpD {t1 t2} (e: Exp t1 t2) : TyD t1 -> TyD t2 := 
 match e in Exp t1x t2x return TyD t1x -> TyD t2x with
 | ID  => fun x => x
 | CONST n => fun _ => n
 | ADD => fun x => Z.add (fst x) (snd x)
 | MUL => fun x => Z.mul (fst x) (snd x)
 | NEG => fun x => Z.opp x
 | COMP f g => fun x => ExpD g (ExpD f x) 
 | INL => fun x => inl x
 | INR => fun x => inr x
 | PAIR f g => fun x => (ExpD f x, ExpD g x)
 | FST => fun x => fst x
 | SND => fun x => snd x
 | TT  => fun _ => tt
 | FF  => fun x => match x with end
 | CASE  f g => fun x => match x with inl a => ExpD f a | inr b => ExpD g b end  
 | CURRY f => fun x y => ExpD f (x, y)
 | EVAL => fun x => fst x (snd x)
 | IN  => fun x => match x with inl _ => nil | inr y => cons (fst y) (snd y) end 
 | OUT => fun x => (shd x, stl x) 
 | FOLD f   => fun x => foldr   (ExpD f) (fst x) (snd x)
 | UNFOLD f => fun x => unfoldr0 (ExpD f) x 
 | DIST  => fun x => match snd x with | inl a => inl (fst x, a) | inr b => inr (fst x,b ) end
 | MAP f => fun x z => exists y, x y /\ ExpD f y = z
 | EMPTY => fun _ z => False
 | SNG   => fun x z => z = x
 | UNION => fun x z => fst x z \/ snd x z
 | FLATTEN => fun x z => exists y, x y /\ y z
 | TENSOR => fun x z => fst z = fst x /\ snd x (snd z) 
 | EQ => fun x => match decidable_equality (fst x) (snd x) with left _ => inl tt | right _ => inr tt end
 end.

(* Small helper definitions ****************************************************************** *)

Definition OPAIR {t1 t2 t3 t4} (e1 : Exp t1 t2) (e2 : Exp t3 t4)
 : Exp (PROD t1 t3) (PROD t2 t4) := PAIR (COMP FST e1) (COMP SND e2).

Definition OCASE {t1 t2 t3 t4} (e1 : Exp t1 t2) (e2 : Exp t3 t4)
 : Exp (SUM t1 t3) (SUM t2 t4) := CASE (COMP e1 INL) (COMP e2 INR).

Definition UNDIST {t1 t2 t3} : Exp (SUM (PROD t1 t2) (PROD t1 t3)) (PROD t1 (SUM t2 t3)) 
 :=  CASE (OPAIR ID INL) (OPAIR ID INR).

Definition NIL {G t} := COMP (COMP (@TT G) INL) (@IN t).

Definition CONS {G t} f (l: Exp G (LIST t)) := COMP (COMP (PAIR f l) INR) (@IN t).

Definition FOLD0  {t t'} (f: Exp (SUM UNIT (PROD t t')) t') : Exp (LIST t) t' 
 := COMP (PAIR TT ID) (FOLD (COMP SND f)).

Definition PFOLD {t t' t''} (f: Exp (PROD t'' (SUM UNIT (PROD (PROD (LIST t) t) t'))) t') : Exp (PROD t'' (LIST t)) t' 
 := COMP (FOLD  (PAIR (COMP SND (CASE NIL (COMP SND FST))) (COMP (OPAIR ID (OCASE TT (PAIR (PAIR (COMP SND FST) FST) (COMP SND SND)))) f))) SND.

Definition UNFOLD1 {t t' t''} (g: Exp (PROD t'' t') (PROD t t')) : Exp (PROD t'' t') (STREAM t) 
 := (@UNFOLD t (PROD t'' t') (PAIR (COMP g FST) (PAIR FST (COMP g SND))) )%type.

Definition PUNFOLD0 {t t'} (f: Exp t' (PROD t (SUM t' (STREAM t)))) : Exp t' (STREAM t)
 := COMP INL (UNFOLD (CASE f (COMP OUT (OPAIR ID INR)))).

Definition PUNFOLD {t t' G} (f: Exp (PROD G t') (PROD t (SUM t' (STREAM t)))) : Exp (PROD G t') (STREAM t) 
 := COMP INL (COMP UNDIST (UNFOLD1 (COMP DIST (CASE f (COMP SND (COMP OUT (OPAIR ID INR))))))).

Definition TRUE {t} : Exp t (SUM UNIT UNIT) := COMP TT INL.

Definition SWAP {A B} : Exp (PROD A B) (PROD B A) := PAIR SND FST.   

Definition DISTHelpher {A B G} : Exp (PROD G (SUM UNIT (PROD A B))) (SUM UNIT (PROD A (PROD G B))) 
 := COMP DIST (OCASE TT (PAIR (COMP SND FST) (PAIR FST (COMP SND SND)))).

Definition DISTHelpher' {A B G} : Exp (PROD G ((PROD A B))) ((PROD A (PROD G B))) :=
 PAIR (COMP SND FST) (PAIR FST (COMP SND SND)).

Definition WongHelper {A B C : Ty} :=
 @PAIR _ A _ (COMP (@FST _ B) (@FST _ C)) (PAIR (COMP FST SND) SND).

(* Equational theory ************************************************************************)

Inductive ExpEq : forall {t1 t2}, Exp t1 t2 -> Exp t1 t2 -> Prop :=
 | REFL : forall {t1 t2} (e: Exp t1 t2), ExpEq e e
 | SYM :  forall {t1 t2} (e1 e2: Exp t1 t2), 
     ExpEq e1 e2 -> ExpEq e2 e1
 | TRANS : forall {t1 t2} (e1 e2 e3: Exp t1 t2), 
     ExpEq e1 e2 -> ExpEq e2 e3 -> ExpEq e1 e3
 | UNITETA : forall {t} (e: Exp t UNIT), ExpEq e TT
 | VOIDETA : forall {t} (e: Exp VOID t), ExpEq e FF
 | FSTBETA : forall {t1 t2 t3} (e1: Exp t1 t2) (e2: Exp t1 t3),
     ExpEq (COMP (PAIR e1 e2) FST) e1
 | SNDBETA : forall {t1 t2 t3} (e1: Exp t1 t2) (e2: Exp t1 t3),
     ExpEq (COMP (PAIR e1 e2) SND) e2
 | PAIRETA : forall {t1 t2 t3} (e: Exp t1 (PROD t2 t3)), 
     ExpEq (PAIR (COMP e FST) (COMP e SND)) e
 | INLBETA : forall {t1 t2 t3} (e1: Exp t1 t2) (e2: Exp t3 t2),
     ExpEq (COMP INL (CASE e1 e2)) e1
 | INRBETA : forall {t1 t2 t3} (e1: Exp t1 t2) (e2: Exp t3 t2),
     ExpEq (COMP INR (CASE e1 e2)) e2
 | CASEETA : forall {t1 t2 t3} (e: Exp (SUM t2 t3) t1), 
     ExpEq (CASE (COMP INL e) (COMP INR e)) e
 | IDL : forall {t1 t2} (e: Exp t1 t2), ExpEq (COMP ID e) e
 | IDR : forall {t1 t2} (e: Exp t1 t2), ExpEq (COMP e ID) e
 | COMPASSOC : forall {t1 t2 t3 t4} (e1: Exp t1 t2) (e2: Exp t2 t3) (e3 : Exp t3 t4),
     ExpEq (COMP (COMP e1 e2) e3) (COMP e1 (COMP e2 e3))
 | FNBETA : forall {t1 t2 t3} (e: Exp (PROD t1 t2) t3), 
     ExpEq (COMP (OPAIR (CURRY e) ID) EVAL) e
 | FNETA : forall {t1 t2 t3} (e: Exp t1 (FN t2 t3)), 
     ExpEq (CURRY (COMP (OPAIR e ID) EVAL)) e

 | COMPCONG : forall {t1 t2 t3} (e1 e3: Exp t1 t2) (e2 e4: Exp t2 t3), 
     ExpEq e1 e3 -> ExpEq e2 e4 -> ExpEq (COMP e1 e2) (COMP e3 e4)
 | CASECONG : forall {t1 t2 t3} (e1 e3: Exp t1 t3) (e2 e4: Exp t2 t3),
     ExpEq e1 e3 -> ExpEq e2 e4 -> ExpEq (CASE e1 e2) (CASE e3 e4)
 | PAIRCONG : forall {t1 t2 t3} (e1 e3: Exp t1 t2) (e2 e4: Exp t1 t3),
     ExpEq e1 e3 -> ExpEq e2 e4 -> ExpEq (PAIR e1 e2) (PAIR e3 e4)
 | CURRYCONG : forall {t1 t2 t3} (e1 e2: Exp (PROD t1 t2) t3),
     ExpEq e1 e2 -> ExpEq (CURRY e1) (CURRY e2)
 | FOLDCONG : forall {t1 t2 G} (e1 e2: Exp (PROD G (SUM UNIT (PROD t1 t2))) t2),
     ExpEq e1 e2 -> ExpEq (FOLD e1) (FOLD e2)

 | DIST1 : forall {t1 t2 t3}, ExpEq (COMP (@DIST t1 t2 t3) (CASE (COMP SND INL) (COMP SND INR))) SND
 | DIST2 : forall {t1 t2 t3}, ExpEq (COMP (@DIST t1 t2 t3) (CASE FST FST)) FST
 | DIST3 : forall {t1 t2 t3}, ExpEq (COMP (OPAIR ID INL) (@DIST t1 t2 t3)) INL
 | DIST4 : forall {t1 t2 t3}, ExpEq (COMP (OPAIR ID INR) (@DIST t1 t2 t3)) INR
 | DIST5 : forall {t1 t2 t3 t4 t5 t6} (f:Exp t1 t2) (g:Exp t3 t4) (h: Exp t5 t6),
    ExpEq (COMP (OPAIR f (CASE (COMP g INR) (COMP h INL))) DIST) 
          (COMP DIST (CASE (COMP (OPAIR f g) INR) (COMP (OPAIR f h) INL)))

 | FOLDBETA : forall {t1 t2 G} (e: Exp (PROD G (SUM UNIT (PROD t1 t2))) t2),
     ExpEq (COMP (OPAIR ID IN) (FOLD e)) (COMP (PAIR FST (COMP DISTHelpher (OCASE TT (OPAIR ID (FOLD e))))) e)

 | FOLDETA : forall {t1 t2 G} (e: Exp (PROD G (SUM UNIT (PROD t1 t2))) t2) (h: Exp (PROD G (LIST t1)) t2),
     ExpEq (COMP (OPAIR ID IN) h) (COMP (PAIR FST (COMP DISTHelpher (OCASE TT (OPAIR ID h)))) e)
     -> ExpEq h (FOLD e)

 | UNFOLDCONG : forall {t1 t2} (e1 e2: Exp t2 (PROD t1 t2)),
     ExpEq e1 e2 -> ExpEq (UNFOLD e1) (UNFOLD e2) 

 | UNFOLDBETA : forall {t1 t2} (e: Exp t2 (PROD t1 t2)),
     ExpEq (COMP (UNFOLD e) OUT) (COMP e ( (OPAIR ID (UNFOLD e))))

 | UNFOLDETA : forall {t1 t2} (e: Exp t2 (PROD t1 t2)) (h: Exp t2 (STREAM t1)),
     ExpEq (COMP h OUT) (COMP e ( (OPAIR ID h)))
     -> ExpEq h (UNFOLD e)

 | MAPID : forall {t}, ExpEq (@ID (SET t)) (MAP ID)
 | MAPCOMP : forall {t1 t2 t3} (f:Exp t1 t2) (g:Exp t2 t3), 
     ExpEq (MAP (COMP f g)) (COMP (MAP f) (MAP g))

 | SNGBETA : forall {t1 t2} (f: Exp t1 t2),
     ExpEq (COMP SNG (MAP f)) (COMP f SNG) 

 | MAPMAP : forall {t1 t2} (f: Exp t1 (SET t2)),
     ExpEq (COMP FLATTEN (MAP f))  (COMP (MAP (MAP f)) FLATTEN) 

 | SNGETA : forall {t}, ExpEq (COMP SNG FLATTEN) (@ID (SET t)) 

 | FLATTENMAPSNG : forall {t}, ExpEq (COMP (MAP SNG) FLATTEN) (@ID (SET t))

 | FLATTENFLATTEN : forall {t}, ExpEq (COMP FLATTEN FLATTEN) (COMP (MAP FLATTEN) (@FLATTEN t))

 | MAPSNDTENSOR : forall {t1 t2}, ExpEq (COMP TENSOR (MAP SND)) (@SND t1 (SET t2))
 | TENSORIDSNG  : forall {t1 t2}, ExpEq (COMP (OPAIR ID SNG) TENSOR) (@SNG (PROD t1 t2))
 | TENSORIDFLATTEN : forall {t1 t2}, ExpEq (COMP (OPAIR (@ID t1) (@FLATTEN t2)) TENSOR)
    (COMP TENSOR (COMP (MAP TENSOR) FLATTEN))

 | MAPTENSOR : forall {t1 t2 t3 t4} (f:Exp t1 t2) (g:Exp t3 t4), 
    ExpEq (COMP TENSOR (MAP (OPAIR f g))) (COMP (OPAIR f (MAP g)) TENSOR)

 | MAPWONG : forall {t1 t2 t3 : Ty}, ExpEq (COMP TENSOR  (MAP (@WongHelper t1 t2 t3 )))
    (COMP WongHelper  (COMP (OPAIR ID TENSOR) TENSOR))

 | UNIONASSOC : forall {t t'} (e f g : Exp t (SET t')), 
    ExpEq (COMP (PAIR (COMP (PAIR e f) UNION) g) UNION) 
    (COMP (PAIR e (COMP (PAIR f g) UNION)) UNION)

 | UNIONCOMM : forall {t t'} (e f : Exp t (SET t')), 
    ExpEq (COMP (PAIR e f) UNION) (COMP (PAIR f e) UNION)

 | UNIONIDEM : forall {t t'} (f : Exp t (SET t')),
    ExpEq (COMP (PAIR f f) UNION) f

 | UNIONEMPTY : forall {t t'} (e f g : Exp t (SET t')),
    ExpEq (COMP (PAIR f (COMP TT EMPTY)) UNION) f

 | MAPCONG : forall {t t'} (e f: Exp t t'), ExpEq e f -> ExpEq (MAP e) (MAP f)

 | EQTRUE1 : forall {t t'} (e f: Exp t t'), ExpEq e f  -> ExpEq (COMP (PAIR e f) EQ) TRUE
 | EQTRUE2 : forall {t t'} (e f: Exp t t'), ExpEq (COMP (PAIR e f) EQ) TRUE -> ExpEq e f 

 | EMPTYTENSOR : forall {G t t'} (f : Exp G t), 
     ExpEq (COMP (PAIR f (COMP (@TT G) EMPTY)) (@TENSOR t t'))
           (COMP (@TT G) EMPTY ) 
 | EMPTYMAP : forall {t t'} (f : Exp t t'),
     ExpEq (COMP (COMP TT EMPTY) (MAP f)) (COMP (@TT t) (@EMPTY t')) 

 | EMPTYFLATTEN : forall {t}, 
     ExpEq (COMP (COMP TT EMPTY) FLATTEN) (COMP (@TT t) (@EMPTY t)).


Theorem axiomsSound : forall t1 t2 (e1 e2: Exp t1 t2), ExpEq e1 e2 -> ExpD e1 = ExpD e2.
Proof.
intros; induction H; simpl in *; try apply functional_extensionality; try congruence; try auto; intros; fold TyD in *.
destruct (ExpD e x); auto.
contradiction.
destruct (ExpD e x); auto.
destruct x; auto.
destruct x; auto.
destruct x; congruence. 
apply functional_extensionality; intros; congruence. 
destruct x; destruct s; auto.
destruct x; destruct s; auto.
destruct x; auto.
destruct x; auto.
destruct x; destruct s; auto.
destruct x; destruct s; auto.

destruct x; simpl in *; induction l; simpl in *; [ apply ((equal_f IHExpEq) (t, inl tt)) | 
 rewrite <- IHl in *; apply ((equal_f IHExpEq) ((t, inr (a, l)))) ].

apply stream_extensionality.  refine ((cofix F o := {|eqhd:= _; eqtl:= _|} ) x).
pose ((equal_f IHExpEq) (o)); simpl in *.
injection e0; auto.
pose ((equal_f IHExpEq) (o)); simpl in *;
injection e0; fold TyD in *; intros pf1 pf2; rewrite pf1; apply F. 

 apply set_extensionality; intros z; intuition; eauto; repeat destruct H; subst; auto. 
 apply set_extensionality; intros z; intuition; eauto; repeat destruct H; subst; auto; eauto. 
 apply set_extensionality; intros z; intuition; eauto; repeat destruct H; subst; auto. 

apply set_extensionality; intros z; intuition. repeat destruct H; subst. simpl in *.
eexists. eexists. eexists. split. eauto. reflexivity. simpl in *. eexists.
split. eauto. eauto.  repeat destruct H; subst. repeat destruct H0. subst; simpl in *.
eexists. eexists. eexists. split. eauto. eauto. auto.

apply set_extensionality; intros z; intuition; repeat destruct H; auto; eexists; eauto. 
apply set_extensionality; intros z; intuition; repeat destruct H; subst; auto; subst; auto.
eexists. split. eexists. split. eauto. reflexivity. simpl. reflexivity. 

apply set_extensionality. intros z. intuition. repeat destruct H.
exists ((fun z0 : TyD t => exists y1 : TyD t -> Prop, x1 y1 /\ y1 z0)). 
split. exists x1. split; auto. exists x0. split; auto.
repeat destruct H. subst. repeat destruct H0. exists x0.
split. exists x1. split; auto. auto.

destruct x; simpl in *. apply set_extensionality. intros z. intuition.
repeat destruct H. subst; auto. exists (t,z). simpl. auto.

destruct x; simpl in *. apply set_extensionality. intros z. destruct z.
simpl.  intuition.  subst.  auto.  congruence. congruence.

destruct x; simpl in *. apply set_extensionality. intros z. destruct z.
simpl.  intuition.  subst. repeat destruct H1. destruct H. 
exists ((fun z : TyD t1 * TyD t2 => fst z = t /\ x (snd z)) ).
simpl. split; auto. exists (t, x). simpl; split; auto.
repeat destruct H. subst. destruct H0. destruct x0; simpl in *. auto.
repeat destruct H. subst. destruct H0. destruct x0; simpl in *. 
subst. exists P0. auto.

destruct x; simpl in *. apply set_extensionality. intros z. destruct z.
simpl.  intuition. repeat destruct H. congruence. 
repeat destruct H. destruct x; simpl in *. 
exists t6. split. auto. congruence. destruct H1. destruct H. subst.
exists (t,x). simpl; split; auto.

destruct x; simpl in *. apply set_extensionality. intros z. destruct z.
simpl. destruct p0; simpl. intuition. repeat destruct H.
destruct x. destruct p. simpl in *. congruence. repeat destruct H.
destruct x. destruct p. simpl in *. congruence. repeat destruct H.
destruct x. destruct p. simpl in *. congruence. subst.
exists (a,b,t4). simpl. intuition. 

apply set_extensionality. intros z. intuition.
apply set_extensionality. intros z. intuition.
apply set_extensionality. intros z. intuition.
apply set_extensionality. intros z. intuition.   
apply set_extensionality. intros z. intuition. 
repeat destruct H0. subst. exists x0. split; auto. rewrite IHExpEq. auto.
repeat destruct H0. subst. exists x0. split; auto. rewrite IHExpEq. auto.

destruct (decidable_equality (ExpD e x) (ExpD f x)). auto. rewrite IHExpEq in n. contradiction.
pose (equal_f IHExpEq x). simpl in e0. clearbody e0. clear IHExpEq.
destruct (decidable_equality (ExpD e x) (ExpD f x)). auto. discriminate.  

apply set_extensionality; intuition.
apply set_extensionality; intuition; repeat destruct H; intuition.
apply set_extensionality; intuition; repeat destruct H; intuition.
Qed.

(* Implementation of sets as lists  ************************************************************** *)
(* todo: upgrade to logical relation *)

Definition TENSOR_list {G t} : Exp (PROD G (LIST t)) (LIST (PROD G t)) 
 := FOLD (COMP DIST (CASE NIL (CONS (PAIR FST (COMP SND FST)) (COMP SND SND)))).

Definition EMPTY_list {t} : Exp UNIT (LIST t) := COMP (COMP TT INL) IN.

Definition SNG_list {t} : Exp t (LIST t) := COMP (COMP (PAIR ID (COMP TT EMPTY_list)) INR) IN.

Definition UNION_list {t} : Exp (PROD (LIST t) (LIST t)) (LIST t) 
 := FOLD (COMP DIST (CASE FST (COMP SND (COMP INR IN)))).

Definition UNION_list2 {t} : Exp (PROD (LIST t) (LIST t)) (LIST t) := COMP SWAP UNION_list.

Definition TENSOR_list2 {G t} : Exp (PROD G (LIST t)) (LIST (PROD G t)) 
 := (FOLD (COMP DIST (CASE (COMP TT EMPTY_list) (COMP  (COMP ((PAIR (PAIR FST (COMP SND FST)) (COMP SND SND))) INR) IN)))).

Definition MAP_list  {t t'} (f: Exp t t') : Exp (LIST t) (LIST t') 
 := FOLD0 (CASE EMPTY_list  (COMP (COMP (PAIR (COMP FST f) SND) INR) IN)).

Definition FLATTEN_list {t} : Exp (LIST (LIST t)) (LIST t) := FOLD0 (CASE EMPTY_list UNION_list2).

Lemma EMPTY_list_ok {t} : listToSet (ExpD (@EMPTY_list t) tt) = ExpD EMPTY tt.
Proof.
  reflexivity.
Qed.

Lemma SNG_list_ok {t} : forall l, listToSet (ExpD (@SNG_list t) l) = ExpD SNG l.
Proof.
 intros. apply set_extensionality. intros e. fold TyD in *.
 intuition. simpl in *. destruct H. auto. contradiction.
 simpl in *. left; auto.
Qed.

Lemma UNION_list_ok {t} : forall x y, listToSet (ExpD (@UNION_list t) (x,y)) = ExpD UNION (listToSet x, listToSet y).
Proof.
 intros. fold TyD in *. apply set_extensionality. intros e.
 intuition. simpl in *. induction y. simpl in *. auto.
 simpl in *. destruct H. subst. right. left. auto.
 simpl in *. pose (IHy H). destruct o. left. auto. right. right. auto.
 simpl in *. destruct H.  induction y. simpl in *. auto.
 simpl in *. right. assumption. induction y. simpl in *. elim H.
 simpl in *. destruct H. subst. left. auto.
 simpl in *. pose (IHy H). right. assumption.
Qed.

Lemma helper3 {t} x y : ExpD (COMP SWAP (@UNION_list t)) (x, y) = ExpD UNION_list (y, x).
Proof.
 fold TyD. intros. simpl. auto.
Qed.

Lemma UNION_list2_ok {t} x y : listToSet (ExpD (@UNION_list2 t) (x,y)) = ExpD UNION (listToSet x, listToSet y).
Proof.
 intros. fold TyD in *. unfold UNION_list2. rewrite helper3.
 rewrite UNION_list_ok.  
 simpl. fold TyD. apply set_extensionality. intros e. 
 intuition.
Qed.

Lemma TENSOR_list2_ok {t t'} x l : listToSet (ExpD (@TENSOR_list2 t t') (x, l)) = ExpD TENSOR (x, listToSet l).
Proof.
 intros. fold TyD in *. apply set_extensionality. intros e. destruct e; simpl.
 intuition. simpl in *. induction l. simpl in *. elim H.
 simpl in *. destruct H. assert (x = t0 /\ a = t1). split;  congruence. destruct H0. subst. auto.
 simpl in *. pose (IHl H). auto.
 simpl in *. induction l. simpl in *. auto.
 simpl in *. destruct H. assert (x = t0 /\ a = t1). split;  congruence. destruct H0.  auto. 
 simpl in *. pose (IHl H). auto. subst.
 simpl in *. induction l. simpl in *. auto.
 simpl in *. destruct H1. subst. left; auto.
 pose (IHl H). auto. 
Qed.

Lemma helper0 {t} : ExpD (@FLATTEN_list t) = @concat (TyD t).
Proof.
 apply functional_extensionality.
 intros x. induction x.
 simpl. auto. rewrite concat_cons.
 rewrite <- IHx. clear IHx.
 induction a. rewrite app_nil_l. simpl. auto.
 unfold FLATTEN_list in *. remember (FOLD0 (CASE EMPTY_list UNION_list2)). 
 rewrite <- app_comm_cons. rewrite <- IHa. clear IHa.
 subst. simpl in *. auto.
Qed.

Lemma helper1 {t} a l : (@ExpD (LIST (LIST t)) (LIST t) (@FLATTEN_list t)
   (@cons (TyD (LIST t)) a l) = a ++ ExpD FLATTEN_list l).
Proof.
 rewrite helper0. simpl. auto.
Qed. 

Lemma FLATTEN_list_ok {t} : forall l, listToSet (ExpD (@FLATTEN_list t ) l) 
  = ExpD FLATTEN (listToSet (map listToSet l)).
Proof.
  intros. unfold listToSet. fold TyD.
  unfold ExpD. fold @ExpD. fold @TyD. apply set_extensionality. intros; intuition.

 Focus 2. repeat destruct H. pose (@in_map_iff _ _ (fun (a : list (TyD t)) (e : TyD t) => In e a) l x0).
 destruct i. pose (H1 H). destruct e. clear H H1. destruct H3. subst.
 clear H2. induction l. simpl in *. auto.
 destruct H1.  subst.  
 rewrite helper1.  apply in_or_app.
 left; auto. rewrite helper1. apply in_or_app.
 right. apply IHl. auto. 

 induction l. simpl in *.  contradiction.
 rewrite helper1 in H. apply in_app_or in H. destruct H.
 exists (listToSet a). split; auto. apply in_map. constructor. auto.
 destruct ( IHl H ). clear IHl. exists x0. destruct H0.
 split; auto. right. auto.
Qed. 

Lemma MAP_list_ok {t t' e} : forall l, listToSet (ExpD (@MAP_list t t' e) l) 
  = ExpD (MAP e) (listToSet l).
Proof.
 intros. apply set_extensionality; fold TyD. intros x.
 induction l; simpl in *; fold @TyD in *. intuition.
 destruct H. destruct H. contradiction. destruct IHl. subst. unfold listToSet in *. 
 intuition. subst. exists a. split. left; auto. auto.
 destruct H1. destruct H0. subst. exists x0. split. right. auto. auto.
 destruct H1. destruct H1. subst. destruct H1. subst. left; auto.
 right. apply H0. exists x0. split; auto.
Qed.

(* tests *)
Eval compute in ExpD (@UNION_list INT) (cons 1 (cons 2 nil), cons 3 (cons 4 nil)).
Eval compute in ExpD (@TENSOR_list2 INT INT) (1, cons 3 (cons 4 nil)).
Eval compute in ExpD (@MAP_list INT INT NEG) (cons 3 (cons 4 nil)).
Eval compute in ExpD (@FLATTEN_list INT) (cons (cons 3 (cons 4 nil)) (cons (cons 1 (cons 2 nil)) nil)).
Eval compute in (ExpD (@TENSOR_list INT INT) (5, cons 1 (cons 2 nil)) ).
Eval compute in FOLD0 (CASE (CONST 0) ADD).
Eval compute in ExpD (@UNION_list2 INT) (cons 1 (cons 2 nil), cons 3 (cons 4 nil)).
Eval compute in ExpD (@TENSOR_list2 INT INT) (1, cons 3 (cons 4 nil)).
Eval compute in ExpD (@MAP_list INT INT NEG) (cons 3 (cons 4 nil)).
Eval compute in ExpD (@FLATTEN_list INT) (cons (cons 3 (cons 4 nil)) (cons (cons 1 (cons 2 nil)) nil)).


(* Lambda calculus form, using dependent de Bruijn indexes ************************************** *)

(* Preliminary: heterogenous lists *)
Section hlist.
 Variable A : Type.
 Variable B : A -> Type.

 Fixpoint hlist (l: list A) : Type := match l with
  | nil => unit
  | a :: b => hlist b * B a
 end.

 Variable elm : A.

 Fixpoint member (ls: list A) : Type :=
  match ls with
    | nil => Empty_set
    | x :: ls' => (x = elm) + member ls'
  end%type.

Definition HFirst ls : member (elm :: ls) := inl eq_refl.

Definition HNext x ls (pf:member ls) : member (x :: ls) := inr pf.


Fixpoint hget {ls : list A} : hlist ls -> member ls -> B elm :=
  match ls with
    | nil => fun {x} idx => match idx with end
    | _ :: ls' => fun {mls} idx => match idx with
                                  | inl pf => match pf with eq_refl => snd mls end
                                  | inr idx' => hget (fst mls) idx'
                                 end
  end.

Definition hhd {ls : list A} :=
   match ls as ls' return hlist ls' -> match ls' return Type with nil => unit | x :: _ => B x end with
     | nil => fun _ => tt
     | _ :: _ => fun x => snd x 
   end.

 Definition htl {ls}  :=
   match ls as ls' return hlist ls' -> match ls' return Type with nil => unit | _ :: ls' => hlist ls' end with
     | nil => fun _ => tt
     | _ :: _ => fun x => fst x
   end.

Definition HNil : hlist nil := tt.

Definition HCons {x ls} (x' : B x) (ls' : hlist ls) : hlist (x :: ls) := (ls', x').

End hlist.

Arguments hlist [A B].
Arguments member [A].
Arguments HNil [A B].
Arguments HCons [A B x ls].
Arguments hhd [A B ls].
Arguments htl [A B ls].
Arguments hget [A B].
Arguments HFirst [A elm ls].
Arguments HNext [A elm x ls].


Inductive exp : list Ty -> Ty -> Type :=
| WEAKEN' : forall {G t} t', exp G t -> exp (t'::G) t 
| EXCH' : forall {G t t' t''}, exp (t::t'::G) t'' -> exp (t'::t::G) t''
| SUBST' : forall {G t t'}, exp (t'::G) t -> exp G t' -> exp G t  

| VAR'   : forall {G t} (pfN: @member Ty t G), exp G t

| CONST' : forall {G}, Z -> exp G INT
| ADD'   : forall {G}, exp G INT -> exp G INT -> exp G INT
| MUL'   : forall {G}, exp G INT -> exp G INT -> exp G INT
| NEG'   : forall {G}, exp G INT -> exp G INT

| INL'   : forall {G t1 t2}, exp G t1 -> exp G (SUM t1 t2)
| INR'   : forall {G t1 t2}, exp G t2 -> exp G (SUM t1 t2)
| FST'   : forall {G t1 t2}, exp G (PROD t1 t2) -> exp G t1
| SND'   : forall {G t1 t2}, exp G (PROD t1 t2) -> exp G t2

| TT'    : forall {G}, exp G UNIT
| FF'    : forall {G t}, exp G VOID -> exp G t

| PAIR'  : forall {G t1 t2}, exp G t1 -> exp G t2 -> exp G (PROD t1 t2)

| CASE'  : forall {G t1 t2 t3}, exp (t1 :: G) t3 -> exp (t2 :: G) t3 -> exp G (SUM t1 t2) -> exp G t3

| CURRY' : forall {G dom ran}, exp (dom :: G) ran -> exp G (FN dom ran)
| EVAL'  : forall {G dom ran}, exp G (FN dom ran) -> exp G dom -> exp G ran

| IN'     : forall {G t}, exp G (SUM UNIT (PROD t (LIST t))) -> exp G (LIST t)
| OUT'    : forall {G t}, exp G (STREAM t) -> exp G (PROD t (STREAM t)) 

| FOLD'  : forall {G t t'}, exp (SUM UNIT (PROD t t')::G) t' -> exp G (LIST t) -> exp G t'
| UNFOLD': forall {G t t'}, exp (t'::G) (PROD t t') -> exp G t' -> exp G (STREAM t) 

| EQ' : forall {G t}, exp G t -> exp G t -> exp G (SUM UNIT UNIT)

| EMPTY' : forall {G t}, exp G (SET t)
| SNG' : forall {G t}, exp G t -> exp G (SET t)
| UNION' : forall {G t}, exp G (SET t) -> exp G (SET t) -> exp G (SET t)

| BIND' : forall {G t t'}, exp G (SET t) -> exp (t :: G) (SET t') -> exp G (SET t').

Fixpoint pfG G := match G with
| nil => UNIT
| a :: b => PROD (pfG b) a
end.

Fixpoint telescope {G t} : @member Ty t G -> Exp (pfG G) t :=
  match G  with
  | nil => fun pf => match pf with end
  | a :: b => fun pf => match pf with
      | inl pf' => match pf' with refl_equal => SND end
      | inr pf' => COMP FST (telescope pf')
    end
  end.

Definition pf : forall {G t}  (e0: exp G t), Exp (pfG G) t.
refine (fix pf {G t} (e0: exp G t) : Exp (pfG G) t :=
 match e0 in exp G' t' return Exp (pfG G') t' with
  | WEAKEN' _ e => COMP FST (pf e)
  | EXCH'   e => COMP (PAIR (PAIR (COMP FST FST) SND) (COMP FST SND)) (pf e)
  | SUBST'  e f => COMP (PAIR ID (pf f)) (pf e) 
  | TT'    => TT
  | EMPTY' => COMP TT EMPTY
  | VAR' v => telescope v
  | NEG'    e => COMP (pf e) NEG
  | INL'    e => COMP (pf e) INL
  | INR'    e => COMP (pf e) INR
  | IN'     e => COMP (pf e) IN
  | OUT'    e => COMP (pf e) OUT
  | FST'    e => COMP (pf e) FST
  | SND'    e => COMP (pf e) SND
  | SNG'    e => COMP (pf e) SNG
  | CURRY'  e => CURRY (pf e)
  | CONST'  n => COMP TT (CONST n)
  | FF'     e => COMP (pf e) FF
  | ADD'    e f => COMP (PAIR (pf e) (pf f)) ADD
  | MUL'    e f => COMP (PAIR (pf e) (pf f)) MUL
  | PAIR'   e f => PAIR (pf e) (pf f)
  | EVAL'   e f => COMP (PAIR (pf e) (pf f)) EVAL
  | FOLD'   e f => COMP (PAIR ID (pf f)) (FOLD   (pf e)) 
  | UNFOLD' e f => COMP (PAIR ID (pf f)) (UNFOLD1 (pf e)) 
  | EQ'     e f => COMP (PAIR (pf e) (pf f)) EQ
  | UNION'  e f => COMP (PAIR (pf e) (pf f)) UNION
  | BIND'   e f => COMP (COMP (PAIR ID (pf e)) (COMP TENSOR (MAP (pf f)))) FLATTEN
  | CASE' l r e => COMP (COMP (PAIR ID (pf e)) DIST) (CASE (pf l) (pf r))
 end). 
Defined.

(** Example: the closed term

  |- (\x:nat. 7 + (\y:nat. x * y)5 )3 : nat 

in de Bruijn (point-full CAML) syntax *)
Definition pfEx1 : exp nil INT :=
EVAL' (CURRY' (ADD' (CONST' 7) 
(EVAL' (CURRY' (MUL' (VAR' (HNext HFirst)) (VAR' HFirst))) (CONST' 5)))) (CONST' 3).

(* the point-free translation *)
Definition pfEx1Trans := pf pfEx1.
Compute pfEx1Trans.
Compute (ExpD pfEx1Trans tt).

(* ************************************************************************* *)


Definition lift2 {G t' t s} (e : exp (s::G) t) : exp (s :: t' :: G) t. 
 pose ( WEAKEN' t' e ). apply EXCH' in e0. assumption.
Defined.
 
Lemma monadlaw_assoc' {G t t' u} : forall (m: exp G (SET t')) 
  (f: exp (t'::G) (SET t)) (g: exp (t::G) (SET u)), 
  ExpD (pf (BIND' m (BIND' f (lift2 g)))) = ExpD (pf (BIND' (BIND' m f) g)) .
Proof.
  intros. simpl in *. fold TyD. apply functional_extensionality. intros env.
  apply set_extensionality; intros x. fold TyD in *. intuition.

  simpl in *. destruct H. destruct H. destruct H. destruct H.  destruct H. 
  subst. destruct H0.  destruct H.  destruct H. 
  destruct x1,x2; simpl in *. destruct H. destruct H. subst. simpl in *.
  exists ( (ExpD (pf g) (t0, t2))).
 intuition. exists (t0, t2). intuition. simpl.
 exists (ExpD (pf f) (t0, t1)). intuition. exists (t0,t1). intuition.


 simpl in *. destruct H. destruct H. destruct H. destruct H.  destruct H. 
  subst. destruct H2.  destruct H.  destruct H. 
  destruct x1,x2; simpl in *. destruct H. destruct H. subst. simpl in *.
  exists ( (fun z : TyD u =>
 exists y : TyD u -> Prop,
   (exists y0 : TyD (pfG G) * TyD t' * TyD t,
      (fst y0 = (t0, t3) /\ ExpD (pf f) (t0, t3) (snd y0)) /\
      ExpD (pf g) (fst (fst y0), snd y0) = y) /\ 
   y z)).
 intuition. exists (t0, t3). intuition. 
 exists (ExpD (pf g) (t0, t1)). intuition. exists (t0,t3,t1). intuition.
Qed.

Lemma monadlaw_empty1 {G t t'} : forall (f: exp (t::G) (SET t')), 
  ExpD (pf (BIND' EMPTY' f)) = ExpD (pf EMPTY').
Proof.
  intros. simpl. fold TyD. apply functional_extensionality. intros x.
  apply set_extensionality. intros e. intuition.
  repeat destruct H; auto.
Qed.

Lemma monadlaw_empty2 {G t t'} : forall (f: exp (t::G) (SET t')), 
  ExpD (pf (BIND' f (@EMPTY' _ (SET t)) )) = ExpD (pf EMPTY').
Proof.
  intros. simpl. fold TyD. apply functional_extensionality. intros x.
  apply set_extensionality. intros e. intuition.
  repeat destruct H; auto.
  subst. auto.
Qed.

Lemma monadlaw_eta {G t} : forall (e: exp G (SET t)), 
  ExpD (pf (BIND' e (SNG' (VAR' HFirst)))) = ExpD (pf e).
Proof.
  intros. simpl. fold TyD. apply functional_extensionality. intros g.
  apply set_extensionality. intros y. intuition.
  repeat destruct H; auto.
  subst. subst. auto. exists (fun z => ExpD (pf e) g z /\ z = y). fold TyD.
  split; auto. exists ((g,y)). split. auto. simpl. apply set_extensionality.
  intros z. split; intros. subst. auto. destruct H0. auto.
Qed.


Lemma monadlaw_beta {G t t'} : forall (e: exp G t) (f: exp (t::G) (SET t')), 
  ExpD (pf (BIND' (SNG' e) f)) = ExpD (pf (SUBST' f e)).
Proof.
 intros. simpl. fold TyD. apply functional_extensionality. intros g.
  apply set_extensionality. intros y. intuition.
  repeat destruct H. subst. destruct x0; simpl in *. subst. auto.
 exists (ExpD (pf f) (g, ExpD (pf e) g)). intuition. simpl.
 exists ((g, ExpD (pf e) g)). intuition.
Qed.

