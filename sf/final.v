(*Final.v*)

Require Export Hoare.
Require Export Smallstep.
Require Export Types.

Hint Constructors multi.


(* IMPERATIVE SUMMATION *)
(*Please write a decorated Imp command c such that the following 
Hoare triple is valid:

 {{X = n}} c {{Y = n*(S n)/2 }}

All arithmetic expressions in c must be constructed from only variables, 
constants, and the plus operation. You can simply write c in plaintext as
a comment in Final.v: just make sure to use the informal syntax for
decorated programs given in Hoare2.v.
You can get 15 pts for writing a command that is correct and 35 pts for 
proving its correctness. For each implication between assertions P -> Q in c, 
include P -> Q in Final.v as a lemma with a proof. *)

(* c is basically the sum of all numbers from 1 to n. It can be written as:

X::= n;;
Y::= 0;;
WHILE not (X = 0) DO
   Y ::= Y + X;;
   X ::= X - 1
END. *)

Definition sumnn: com:=
Y::=(ANum 0);;
WHILE BNot (BEq (AId X) (ANum 0)) DO
    Y ::= APlus (AId Y) (AId X);;
    X ::= AMinus (AId X) (ANum 1)
END.

(*Decorated proof of c: 

      {{ True }} ->>
         {{ n = n }}
   X::= n;;
      {{ X = n }} ->>
         {{ X = n /\ 0 = 0 }}
   Y::= 0;;
      {{ X = n /\ Y = 0}} ->>
         {{ Y + (X*(X+1)/2) = n*(n + 1)/2 }}
   WHILE (X <> 0) DO
      {{ Y + (X*(X+1)/2) = n*(n + 1)/2 /\  X <> 0 }} ->>
         {{ (Y+X) + ((X-1)*X/2) = n*(n + 1)/2 }}
      Y ::= Y + X;;
        {{ Y + ((X-1)*X/2) = n*(n + 1)/2  }} 
      X ::= X - 1
        {{ Y + (X*(X+1)/2) = n*(n + 1)/2 }}
   END.
     {{ Y + (X*(X+1)/2) = n*(n + 1)/2 /\ X = 0}} ->>
        {{ Y = n * (n + 1)/2 }}
*)

(* Changing all the divisions into multiplications as division is not supported.
 Hence, Y + (X*(X+1)/2) = n*(n + 1)/2 becomes (st Y * 2) + (st X)*((st X) +1) = n*(n + 1)
by multiplying by 2 on both sides*)

Lemma c1: forall n, ( fun st => st X = n /\ st Y = 0) ->>
         ( fun st => (st Y * 2) + (st X)*((st X) +1) = n*(n + 1) ).
Proof.
intros n st.
intros.
destruct H.
rewrite H0, H.
omega.
Qed.

Lemma plus_2: forall a, a*2 = a+a.
Proof.
intros.
induction a.
reflexivity.
simpl.
apply f_equal.
rewrite <- plus_n_Sm.
rewrite IHa.
reflexivity.
Qed.

Lemma c2: forall n, (fun st => (st Y * 2) + (st X)*((st X) +1) = n*(n + 1) /\ st X <> 0) ->>
         ( fun st => (st Y + st X) * 2 + (st X -1)*st X = n*(n + 1) ).
Proof.
intros n st H.
destruct H.
rewrite mult_minus_distr_r.
rewrite mult_1_l.
rewrite mult_plus_distr_r.
rewrite plus_2 with (a:= st X).
assert ((st X + st X)-st X = st X).
rewrite minus_plus. reflexivity.
rewrite plus_permute.
rewrite plus_comm.
rewrite plus_permute.
rewrite plus_assoc.
assert (forall a b, a<>0 -> a + (b-a ) = b).
unfold not.
intros. induction b. unfold not in H2. admit. destruct a. omega. simpl. apply f_equal. admit.
rewrite plus_permute.
rewrite H2 with (a:= st X) (b:= (st X * st X)).
rewrite mult_plus_distr_l in H.
rewrite mult_1_r in H.
assumption.
assumption.
Qed.

Lemma c3: forall n, (fun st => (st Y * 2) + (st X)*((st X) +1) = n*(n + 1) /\ st X = 0) ->>
         ( fun st => st Y * 2 = n*(n + 1) ).
Proof.
intros n st.
intros.
destruct H.
rewrite H0 in H.
simpl in H.
rewrite plus_0_r in H.
assumption.
Qed.


Theorem sum_of_natural_numbers_correct : forall n,
  {{fun st => True}}
  sumnn
  {{fun st => st Y *2 = n * (n+1) }}.
Proof.
intros.
unfold sumnn.
eapply hoare_seq. 
eapply hoare_consequence_post.
apply hoare_while.
  Case "Loop body preserves invariant".
    eapply hoare_seq.
    apply hoare_asgn.
    eapply hoare_consequence_pre. 
    apply hoare_asgn.
    intros st [HT Hbp]. unfold assn_sub. simpl.
  Admitted.



(*TYPES*)

(*In this problem, you'll extend the language of terms tm defined in Types.v with a construct for representing
a sum of terms.
Syntax (5 pts): Extend the syntax of tm so that for all terms t0; t1 belongs to tm, tplus t0 t1 belongs to tm.
Small-step semantics (5 pts): Extend the small-step semantics of tm defined by step so that:
 1. For each numeric value v belongs to nvalue, tplus 0 v => v.
 2. For all numeric values v0; v1 belongs to nvalue, tplus (tsucc v0) v1 ) tplus v0 (tsucc v1).*)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm
  | tplus : tm -> tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.  
Hint Unfold extend.

Reserved Notation "t1 '==>' t2" (at level 40).


Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')
  | ST_PlusZero : forall t,
       nvalue t -> tplus tzero t ==> t
  | ST_Plus1 : forall t1 t2,
       nvalue t1 -> nvalue t2 ->
       tplus (tsucc t1) t2 ==> tplus t1 (tsucc t2)
  | ST_Plus2 : forall t1 t2 t1',
       t1 ==> t1' ->
       tplus t1 t2 ==> tplus t1' t2
  | ST_Plus3 : forall t1 t2 t2',
       t2 ==> t2' ->
       tplus t1 t2 ==> tplus t1 t2'

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.
Hint Unfold stuck.

(*Types (40 pts): 
Extend the typing relation of tm defined by has type so that for all terms t0; t1 belongs to Nat,
tplus t0 t1 belongs to Nat. Prove progress and preservation for has type extended for tplus.
You can write the proofs any way you choose, but one manageable workflow would be to first finish the
proofs of progress and preservation for tm included in Types, and then extend each proof with cases 
for terms mconstructed from tplus.
You can get 5 pts for writing correct type inference rules and 35 pts for proving their correctness. *)

Inductive ty : Type := 
  | TBool : ty
  | TNat : ty.

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       |- ttrue \in TBool
  | T_False : 
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero : 
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool
  | T_Plus : forall t1 t2,
       |- t1 \in TNat ->
       |- t2 \in TNat ->
       |- tplus t1 t2 \in TNat

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type.

Lemma bool_canonical : forall t,
  |- t \in TBool -> value t -> bvalue t.
Proof.
  intros t HT HV.
  inversion HV; auto.
  induction H; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in TNat -> value t -> nvalue t.
Proof.
  intros t HT HV.
  inversion HV.
  inversion H; subst; inversion HT.  
  auto.  
Qed.


Theorem progress1 : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  induction HT.
  Case "T_True".
    left. left. constructor.
  Case "T_False".
    left. left. constructor.
  Case "T_If".
    right. inversion IHHT1; clear IHHT1.
    SCase "t1 is a value".
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2.
      constructor.
      exists t3.
      constructor.
    SCase "t1 can take a step".
      inversion H as [t1' H1].
      exists (tif t1' t2 t3).
      constructor.
      assumption.
  Case "T_Zero".
    left. right. constructor.
  Case "T_Succ".
    inversion IHHT; subst.
    SCase " t1 is a value".
       left.
       apply (nat_canonical t1 HT) in H.
       right. constructor. assumption.
    SCase "t1 can take a step".
       right. 
       inversion H; subst.
       exists (tsucc x)...
   Case "T_Pred".
      inversion IHHT; subst.
      SCase " t1 is a value".
         right.
         apply (nat_canonical t1 HT) in H.
         inversion H; subst.
         exists tzero...
         exists t...
      SCase "t1 can take a step".
         right. 
         inversion H; subst.
         exists (tpred x)...
   Case "T_Iszero".
      inversion IHHT; subst.
      SCase " t1 is a value".
         right.
         apply (nat_canonical t1 HT) in H.
         inversion H; subst.
         exists ttrue...
         exists tfalse...
      SCase "t1 can take a step".
         right. 
         inversion H; subst.
         exists (tiszero x)...
   Case "T_Plus".
      inversion IHHT1; subst.
      SCase " t1 is a value".
         inversion IHHT2; subst.
         SSCase "t2 is a value".
             right. 
             apply (nat_canonical t1 HT1) in H.
             apply (nat_canonical t2 HT2) in H0.
             inversion H; subst.             
             exists t2...
             exists (tplus t (tsucc t2))...
         SSCase "t2 can take a step".
             right. 
             apply (nat_canonical t1 HT1) in H.
             inversion H0; subst.             
             exists (tplus t1 x)...      
      SCase "t1 can take a step".
         right. 
         inversion IHHT2; subst.
         SSCase "t2 is a value".
             apply (nat_canonical t2 HT2) in H0.
             inversion H; subst.
             exists (tplus x t2)...
         SSCase "t2 can take a step".
             inversion H; subst.
             exists (tplus x t2).
             constructor.
             assumption.
Qed.

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT; intros t' HE; try (solve by inversion).
    Case "T_If". inversion HE; subst; clear HE.
      SCase "ST_IFTrue". assumption.
      SCase "ST_IfFalse". assumption.
      SCase "ST_If". apply T_If; try assumption.
        apply IHHT1; assumption.
    Case "T_Succ". inversion HE; subst.
        apply T_Succ. apply IHHT. assumption.
    Case "T_Pred". inversion HE; subst.
        apply T_Zero.
        inversion HT; subst. assumption.
        apply T_Pred. apply IHHT in H0. assumption.
    Case "T_Iszero". inversion HE; subst.
        constructor. constructor. apply T_Iszero.
        apply IHHT in H0. assumption.
    Case "T_Plus". inversion HE; subst.
        assumption. 
        apply T_Plus. inversion HT1; subst. assumption.
        apply T_Succ. assumption.        
        apply T_Plus. apply IHHT1 with (t':=t1'). assumption.
        assumption.
        apply T_Plus. assumption.
        apply IHHT2 with (t':=t2'). assumption.
Qed.



















