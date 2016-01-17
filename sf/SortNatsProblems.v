(** * Sorting *)

(** In this module, we'll implement insertion sort, then state and
prove its correctness. As a warm-up, we'll first write a verified
insertion sort that operates over only lists of [nat]s. We'll then
generalize to an implementation that operates on polymorphic lists.

This module will only rely on the definitions introduced up to
MoreLogic. That said, feel free to use Coq tactics discussed later in
the text, such as auto.

*)

Require Export MoreLogic.

(** * Permutations *)

(** [perm] (5 pts): every sorting function should return a result that
is a permutation of its input.  We'll first define the permutation
relationship over lists. The dependency between permutations and the
type of data stored in a list is very loose, so we'll go ahead and
just define a permutation once, generalized over the type of data
stored in the lists that we permuate.

Please define a [Prop]osition [perm] paramaterized on:

(1) a type [T];

(2) two lists of type [list T].

For each type [T]:

(1) [perm T] should hold over the empty lists of type [T]:

(2) for each element [n] of type [T] and all lists [l], [l0], and [l1]
of [T] values, if [l] permutes to [l0 ++ l1], then [n :: l] permutes
to [l0 ++ n :: l1].

*)

(* DEFINE perm HERE *)

Inductive perm (T:Type): list T -> list T -> Prop:=
| perme : perm T [] []
| permp : forall (l l0 l1 :list T) (n: T), perm T l (l0++l1) -> perm T (n::l) (l0++n::l1).

(** [perm_refl (5 pts), perm_trans (20 pts)]: for each type [T], [perm
T] defines a binary relation over [list T] that is in fact an
equivalence relation. It'll help in some of our later proofs to use
the facts that [perm T] is reflexive and transitive, so please prove
these facts now. *)

Lemma perm_refl : forall T l, perm T l l.
Proof.
  intros.
  induction l.
  Case "perme".
      apply perme.
  Case "permp".
      apply permp with (l0:=[]) (l1:= l) (n:=x).
      simpl.
      assumption.      
  Qed.

Lemma null_app: forall (T:Type) (l0 l1: list T),
[] = l0++l1 -> l0 = [] /\ l1=[].
Proof.
induction l0.
split.
reflexivity.
generalize dependent l1.
induction l1.
reflexivity.
intros.
inversion H.
intros.
inversion H.
Qed.


Lemma perm_trans :
  forall T l0 l1 l2, perm T l0 l1 -> perm T l1 l2 -> perm T l0 l2.
Proof.
intros.
generalize dependent l0.
induction H0; intros.
assumption.
inversion H0; subst.
apply null_app in H3.
destruct H3.
rewrite H1, H2.
simpl.
assumption.
rewrite <- H1 in H0.
apply permp with (n:=n0) in H0.
inversion H; subst.
admit.

  Qed.

(** * Sorting [list nat]'s

In this module, we'll define when one list of [list nat]'s is a
sorting of another, define insertion sort over [nat list]'s, and prove
that our definition returns a sorting of its input. *)

Module SortingNats.

(** ** Defining Sortedness 

We'll now formulate under what conditions one [list nat] is a valid
sorting of another [list nat].  *)

(** [nat_sorted] (10 pts): please define a [Prop] named [nat_sorted]
over a single [list nat]. [nat_sorted] should hold under one of the
following conditions:

(1) [nat_sorted] holds for the empty list;

(2) for each [nat] [n], [nat_sorted] holds for [[n]];

(3) for all [nat]s [m] and [n] and each [list nat l], if [m <= n] and
[nat_sorted] holds for [n :: l], then [nat_sorted] holds for [m :: n
:: l].

Note that this definition formalizes only "local" sortedness, not
"strong" sortedness. *)

(* TODO: define nat_sorted here. *)

Inductive nat_sorted: list nat -> Prop:=
| natse : nat_sorted []
| natsn : forall (n:nat), nat_sorted [n]
| natsmn : forall (m n: nat) (l: list nat), m<= n -> nat_sorted (n::l) -> nat_sorted (m::n::l).

(** [is_nat_sorting] (5 pts): now, please formulate when one [list
nat] is a sorting of another [list nat].

For [nat list]'s [l0] and [l1], [l1] is a sorting of [l0] if both of
the following conditions hold:

(1) [l1] is a sorted [list nat];

(2) [l1] is a permutation of [l0]. *)

(* TODO: define is_nat_sorting here. *)

Definition is_nat_sorting (l0 l1:list nat): Prop:= nat_sorted l1 /\ perm nat l0 l1.

(** ** Defining insertion sort 

We'll now define an implementation of insertion sort over [nat
list]'s. *)

(** [ble_nat_dec] (20 pts): one natural way to implement insertion
sort would be to use [ble_nat], which returns a [bool] that denotes if
its first input is less-than-or-equal-to the second. We could write an
implemenation using [ble_nat] that is correct, but its correctness
would be awkward to prove, because we would have to define, prove, and
use many simple lemmas for translating between the [bool] results of
[ble_nat] and the actual ordering over [ble_nat]'s inputs.

In the unit on evidence-carrying Booleans, we saw that a similar
awkwardness can be neatly sidestepped for reasoning about tests of
equality over [nat]s with [beq_nat] by writing and using a proof
[beq_nat_dec] that for all [nat]'s [m] and [n], either constructs a
proof that [m = n] or [m <> n].

To write and prove the correctness of our sorting function, we'll
write a similar proof [ble_nat_dec] that for all [nat]'s [m] and [n],
either constructs a proof that [n <= m] or that [m <= n]. 

The theorem is alrady stated. Please complete the proof.
*)


Theorem ble_nat_dec : forall (n m : nat), { n <= m } + { m <= n }.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      left. apply O_le_n.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. apply O_le_n.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply n_le_m__Sn_le_Sm. assumption.
      right. apply n_le_m__Sn_le_Sm. assumption.
Defined.

(** [nat_insert] (5 pts) takes:

(1) a [nat] [n];

(2) a sorted [nat list] [l].

[nat_insert] returns a sorted [list nat] with [n] inserted into [l].

Please define [nat_insert]. One natural definition is a [Fixpoint]
that only uses [ble_nat_dec].  *)

(* TODO: complete definition. *)
Fixpoint nat_insert n l : list nat:= 
match l with
| [] => [n]
| x :: t1 => if ble_nat_dec n x
             then (n::x::t1)
             else (x::(nat_insert n t1))
end.

(** [nat_insert_sort] (5 pts) takes:

(1) a [list nat] [l]

[nat_insert_sort] returns a sorting of [l].

Please write [nat_insert_sort]. One natural definition is a [Fixpoint]
that only uses [nat_insert].  *)

(* TODO: complete definition *)
Fixpoint nat_insert_sort l : list nat:=
match l with
| [] => []
| [x] => [x]
| h::t1 => nat_insert h (nat_insert_sort t1)
end.

Example sort1 : nat_insert_sort [1;4;2;3;5] = [1;2;3;4;5].
Proof. simpl. reflexivity. Qed.

Example sort2 : nat_insert_sort [5;4;3;2;1] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example sort3 : nat_insert_sort [1;2;3;4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

(** ** Proving correctness *)

(** [insert_sorted] (10 pts): we now have a complete definition of
insertion sort over [list nat]'s, [nat_insert_sort]; we want to prove
that it returns a sorting of its input.

One observation that helps to simplify the proof is that we can prove
that (1) [nat_insert_sort] produces a permutation and (2)
[nat_insert_sort] produces a sorted result completely
independently. Furthermore, the proofs of each sub-property can be
broken down into a key lemma about [insert], which is used in the
proof of the sub-property for [nat_insert_sort].

We'll start by proving that [nat_insert] takes each [nat] and sorted
list to a sorted list.  *)

Lemma blah: forall l n x, 
x<=n -> nat_sorted (x::l) -> nat_sorted (nat_insert n (x::l)) -> nat_sorted (x::nat_insert n l).
Proof.
intros.
induction l.
simpl.
constructor.
assumption. constructor.
simpl.
destruct (ble_nat_dec n x0) eqn:B.
constructor. assumption. constructor. assumption.
inversion H0; subst. assumption.
constructor.
inversion H0; subst. assumption.


Admitted.

Lemma insert_sorted : forall l n, nat_sorted l -> nat_sorted (nat_insert n l).
Proof.
intros.
generalize dependent n.
induction l.
simpl.
constructor.
intros.
simpl.
destruct (ble_nat_dec n x) eqn:B.
constructor.
assumption. assumption.
inversion H; subst.
simpl.
constructor.
assumption. constructor.
inversion H; subst.
induction H.
simpl.
(*constructor.
simpl.
destruct (ble_nat_dec n n0) eqn:B.
constructor.
assumption. constructor.
constructor. assumption. constructor.
destruct (ble_nat_dec n m) eqn:B1.
simpl.
rewrite B1.
constructor. assumption.
constructor. auto.
assumption.
destruct (ble_nat_dec n n0) eqn:B.
simpl.
rewrite B1.
rewrite B.
simpl in IHnat_sorted.
rewrite B in IHnat_sorted.
constructor. assumption.
constructor. auto. assumption.
simpl.
rewrite B1.
rewrite B.

constructor. assumption.
induction l.
simpl. constructor. assumption. constructor.
simpl.*)

Admitted.


(** [insertion_sorted] (5 pts): now, prove that [nat_insert_sort]
produces a sorted result. One natural proof requires only about 10
lines, using [insert_sorted]. *)

Lemma insertion_sorted : forall l, nat_sorted (nat_insert_sort l).
Proof.
intros.
induction l.
simpl.
constructor.
simpl.
destruct l.
constructor.
apply insert_sorted.
assumption.
Qed.

(** [insert_perm] (10 pts): now, prove that [nat_insert] takes each
[nat] [n] and [list nat] [l] to a permutation of [n :: l]. One natural
proof uses [perm_refl]. *) 


Lemma insert_perm : forall l n, perm nat (n:: l) (nat_insert n l).  
Proof.
intros.
induction l.
simpl.
apply perm_refl.
simpl.
destruct (ble_nat_dec n x) eqn:B.
apply perm_refl.
inversion IHl; subst.
apply permp with (n:=x) in H0.
apply permp with (n:=n) in H0.
inversion H0; subst.
simpl.
destruct (ble_nat_dec n x) eqn:B1.
(*apply perm_refl.
rewrite <- H2.
apply permp.


rewrite l0 in B.
inversion B.
simpl in IHl.
inversion IHl; subst.
inversion H0.
inversion H.
apply perm_refl. *)
Admitted.

(** [insertion_perm] (10 pts): now, prove that [nat_insert_sort]
permutes its input. One natural proof is only ~15 lines, and uses
[perm_trans].  *)

Lemma insertion_perm : forall l, perm nat l (nat_insert_sort l).
Proof.
intros.
induction l.
constructor.
simpl.
destruct l.
simpl.
apply perm_refl.
inversion IHl; subst.
simpl.
Admitted.

(** [insertion_sorting] (5 pts): finally, prove that [nat_insert_sort]
returns a sorting of its input. One natural proof is extremely
straighforward and uses [insertion_sorted] and [insertion_perm]. *)

Theorem insertion_sorting :
  forall l, is_nat_sorting l (nat_insert_sort l).
Proof.
intros.
unfold is_nat_sorting.
split.
apply insertion_sorted.
apply insertion_perm.
Qed.

End SortingNats.

(** * Sorting Polymorphic [list]s 

If you've completed all of the definitions up to this point, then
you've actually defined and proven the correctness of an
implementation of insertion sort for [nat list]'s.

However, sorting functions included in practical libraries are
typically polymorphic: they sort lists of arbitrary data of the same
type, as long as a user provides some function for ordering any two
elements of the type of values stored in the list.

In this next module, we'll define, then state and prove the
correctness of, sorting functions over polymorphic lists. If in
[SortingNats], you (1) defined [nat_insert] to only operate on
elements by applying [ble_nat_dec] and (2) wrote proofs that only
inspected values in a list by considering the result of applying
[ble_nat_dec] to the values, then your proofs from [SortingNats]
should go through after only superficial changes to various names. *)

Module SortingGen.

(** ** Defining sortedness

We'll now define sortedness over polymorphic lists.
*)

(** [binrel]: [binrel]'s will generalize the less-than-or-equal
ordering over [nat]'s used in the specfication of [nat_insert_sort].

For type [T], let [binrel T] be a binary relation over [T],
represented as a function that takes two values of type [T] and
returns a [Prop]: *)

Definition binrel (T : Type) := T -> T -> Prop.

(** [sorted] (5 pts): please generalize [nat_sorted] to be defined
over polymorphic lists.

For type [T], binary relation [ord] over [T], and list l of type [list
T], the [Prop]osition [sorted T ord l] should hold under conditions
directly analogous to those given for [nat_sorted].  *)

(* TODO: complete definition. *)

(** [is_sorting] (5 pts): please generalize [is_nat_sorting] to be
defined over polymorphic lists.

For type [T], binary relation [ord] over [T], and lists [l0] and [l1]
over values of type [T], the [Prop]osition [is_sorting T ord l0 l1]
should hold if all of the following conditions hold:

(1) [l1] is sorted under [T] and [ord];

(2) [l0] permutes to [l1].
*)

(* TODO: complete definition. *)

(** ** Defining insertion sort 

We'll now define an insertion sort over polymorphic lists.  *)

(** [comparitor]: [comparitor]'s will generalize [ble_nat_dec] as used
in the definition of [nat_insert].

For type [T] and [ord] a binary relation over [T], let a comparitor
over [T] and [ord] be a function that for all elements [a] and [b] or
type [T], returns either evidence that the ordered pair [(a, b)] is in
[ord] or the pair [(b, a)] is in [ord]. *)

Definition comparitor { T } (ord: binrel T) :=
  forall (a b : T), { ord a b } + { ord b a }.

(** [insert] (5 pts): please generalize [nat_insert] to operate over
polymorphic lists.

[insert] should take:

(1) a type [T];

(2) a binary relation [ord] over [T];

(3) a comparitor [ble_dec] over [T] and [ord];

(4) an element [n] of type [T];

(5) a list [l] of [T] data.

If [l] is sorted, then [insert] returns a sorted list with [n]
inserted into [l].

You can define [insert] by essentialy replacing uses of [ble_nat_dec]
in [nat_insert] with uses of [ble_dec]. *)

(* TODO: complete definition. *)

(** [insert_sort] (5 pts): please generalize [nat_insert_sort] to
operate over polymorphic lists.

[insert_sort] sould take:

(1) a type [T];

(2) a binary relation [ord] over [T];

(3) a comparitor [ble_dec] over [T] and [ord];

(4) a list [l] of [T] values.

[insert_sort] should return a sorting of [l] under [T] and [ord].

You can define [insert_sort] by essentially replacing uses of
[nat_insert] in [nat_insert_sort] with [insert]. *)

(* TODO: complete definition. *)

(** ** Proving correctness *)

(** [insert_sorted] (5 pts): please generalize
[SortingNats.insert_sorted] for [insert], and prove the claim.

[insert_sorted] should claim that for each type [T], binary relation
[ord] over [T], and comparitor [ble_dec] over [T] and [ord], if [l] is
sorted under [T] and [ord], then [insert ble_dec n l] is sorted under
[T] and [ord].  *)

(* TODO: define and prove. *)

(** [insertion_sorted] (5 pts): please generalize
[SortingNats.insertion_sorted] for [insert_sort], and prove the claim.

[insertion_sorted] should claim that for each type [T], binary
relation [ord], comparitor [ble_dec] over [T] and [ord], and list [l] of
type [list T], [insert_sort T ord ble_dec l] is sorted.

The proof of insertion_sorted can be structured almost identically to
a proof of [SortingNats.insertion_sorted]. *)

(* TODO: define and prove. *)

(** [insert_perm] (5 pts): please generalize [SortingNats.insert_perm]
for [insert], and prove the claim.

[insert_perm] should claim that for each type [T], binary relation
[ord] over [T], comparitor [ble_dec] over [T] and [ord], element [n]
of type [T], and list [l] of [T] values, [n :: l] permutes to [insert
T ord ble_dec n l].

The proof can be structured almost identically to a clean proof of
[insert_perm].  *)

(* TODO: define and prove. *)

(** [insertion_perm] (5 pts): please generalize
[SortingNats.insertion_perm] to claim that [insert_sort] returns a
permutation of its input, and then prove the claim.

[insertion_perm] should claim that for each type [T], binary relation
[ord] over [T], comparitor [ble_dec] over [T] and [ord], and list [l] of
values of type [T], [l] permutes to [insert_sort ble_dec l]. *)

(* TODO: define and prove. *)
  
(** [insertion_sorting] (5 pts): please generalize
[SortNats.insertion_sorting] to claim the correctness of
[insert_sort], then prove the claim.

[insertion_sorting] should claim that for each type [T], binary
relation [ord] over [T], and comparitor [ble_dec] over [T] and [ord],
[insert_sort T ord ble_dec l] is a sorting of [l].

The proof can be structured very similarly to the proof of
[SortNats.insertion_sorting].  *)

(* TODO: define and prove. *)

(** It's now trivial to define [nat_insert_sort] as an application of
[insert_sort]: *)

(*Definition nat_insert_sort := insert_sort (SortingNats.ble_nat_dec).

(** We could also prove that the [nat_insert_sort] that we wrote by
hand is equivalent to the version produced as application of
[insert_sort]. I.e., we could prove: *)

Theorem eq_sorts :
  forall l, SortingNats.nat_insert_sort l = nat_insert_sort l. *)

(** However, assuming that the two programs were written with the same
structure, this proof wouldn't be terribly interesting. *)

(** Having defined and verified implementations of insertion sort, a
natural next step is to determine what is involved to prove other
favorite sorting algorithms, namely ones with tighter worst-case
performance bounds, such as [quicksort] and [mergesort].

These can be implemented and verified in Coq; however, defining
implementations that will even be accepted by the Coq compiler is
actually non-trivial. The complexity stems from the fact that the
natural definition of [mergesort] recurses on a split of its input
list, but the Coq compiler cannot determine that this definition of
[mergesort] performs well-founded recursion (compare to insertion
sort, which recurses on the tail of a list).

If you're interested in learning how to overcome this problem, Coq
provides a verified implementation of [mergesort] in its standard
library <https://coq.inria.fr/library/Coq.Sorting.Mergesort.html>. *)

End SortingGen.
