require import Bool Int Real DInterval Distr AllCore IntExtra RealExtra DBool.
require import List Finite StdOrder StdBigop Dexcepted.
require Dice_sampling.

search dinter.

module Dice = {
  var x : int
  proc throw() : bool = {
  x <$ [1 .. 6];
    return x = 6;
  }
}.

search mu.

module Dice2 = {
  var x : int
  proc throw() : int = {
  x <$ [1 .. 6];
  return x;
  }
}.

lemma Dice1_2equiv &m1 &m2 :
    
    Pr[Dice2.throw() @ &m1 : res = 6 ] =
    Pr[Dice.throw() @ &m2 : res].
    proof.
      byequiv. proc. auto. trivial. trivial.
qed.

lemma uniformDice2 : forall &m (x : int), x \in [1 .. 6] =>
    Pr[Dice2.throw() @ &m : res = x] = 1%r / 6%r.
    proof.
      progress. byphoare. proc. rnd. skip. simplify. search dinter.
      rewrite dinter1E. simplify. smt. trivial. trivial.
  qed.
    
lemma uniformDice &m :
    Pr[Dice.throw() @ &m : res] = 1%r / 6%r.
    proof.
      byphoare. proc. wp. rnd. skip. simplify. rewrite dinter1E; by done. done. done.
  qed.

 (* lemma uniformDiceF (x:int, b:bool) &m :
    Pr[Dice.throw() @ &m : !res] = 5%r / 6%r.
    proof.
      byphoare. proc. wp. rnd. skip. simplify. rewrite supp_dinter.
  qed.*)

lemma uniformEqual : forall &m1 (x : int), x \in [1 .. 6] => forall &m2 (y : int), y \in [1 .. 6] => Pr[Dice2.throw() @ &m1 : res = x] = Pr[Dice2.throw() @ &m2 : res = y].
    proof.
    move => &m1 x xrange &m2 y yrange.
      rewrite (uniformDice2 &m1 x). assumption. rewrite (uniformDice2 &m2 y). assumption. trivial.
    qed.

  lemma dicebigger10 (x:int) :
    phoare[Dice.throw : true ==> res] >= (1%r/10%r).
    proof.
      proc. wp. rnd. skip.  simplify. rewrite dinter1E. smt.
qed.

lemma halfdice (x:int) &m :
    Pr[Dice2.throw() @ &m : res =1 \/ res = 2 \/ res = 3] = 1%r/2%r.
    proof.
      byphoare. proc. rnd. simplify. skip. simplify. auto. search mu.