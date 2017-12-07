require import StdRing StdOrder Distr AllCore DBool.
require (*    *) CyclicGroup. 

clone export CyclicGroup as G.

type ptext = group.
type ctext = group * group.
type pkey  = group.
type skey  = F.t.

op q : { int | 0 < q } as q_pos.

(* 1. Defining a scheme, an adversary and the chosen plaintext attack *)

module type Scheme = {
  proc keygen() : pkey * skey
  proc encrypt(pk:pkey, m:ptext) : ctext
  proc decrypt(sk:skey, c:ctext) : ptext option
}.

module type Adversary = {
  proc choose(pk:pkey) : ptext * ptext
  proc guess(c:ctext) : bool
}.

module CPA (S:Scheme) (A:Adversary) = {
  proc main() : bool = {
  var m1, m0, c, pk, sk, b, b';

    (pk, sk) = S.keygen();
    (m0, m1) = A.choose(pk);
    b =$ {0,1};
    c = S.encrypt(pk, b ? m1 : m0);
    b' = A.guess(c);
    return (b = b');
  }
  }.
  
(* 2. Defining an attacker and games for the decisional Diffie-Hellman problem *)
  
  module type DDHAdversary = {
    proc guess(gx gy gz:G.group): bool
  }.

  module DDH0 (A:DDHAdversary) = {
    proc main() : bool = {
      var b, x, y;
      x = $FDistr.dt;
      y = $FDistr.dt;
      b = A.guess(g ^ x, g ^ y, g ^ (x*y));
      return b;
    }
  }.

  module DDH1 (A:DDHAdversary) = {
    proc main() : bool = {
      var b, x, y, z;

      x = $FDistr.dt;
      y = $FDistr.dt;
      z = $FDistr.dt;
      b = A.guess(g ^ x, g ^ y, g ^ z);
      return b;
    }
  }.
  
(* 3. Setting up a module for the ElGamal cryptosystem *)
  
module ElGamal : Scheme = {
  proc keygen(): pkey * skey = {
  var pk:pkey;
  var sk:skey;
    sk <$ FDistr.dt;
    return (g ^ sk, sk);
  }

  proc encrypt(pk:pkey, m:ptext): ctext = {
    var y;
    y <$ FDistr.dt;
    return (g ^ y, pk ^ y * m);
  }

  proc decrypt(sk:skey, c:ctext): ptext option = {
    var gy, gm;
    (gy, gm) <- c;
    return Some (gm * gy^(-sk));
  }
}.

    (* 4. Reduction from PKE adversary to DDH adversary *)
    
module DDHAdv (A:Adversary) = {
  proc guess (gx, gy, gz) : bool = {
  var m0, m1, b, b';
    (m0, m1) <- A.choose(gx);
      b <$ {0,1};
      b' <@ A.guess(gy, gz * (b?m1:m0));
    return (b' = b);
  }
}.

            (* 5. Proof of correctness for ElGamal *)

section Correctness.
local module Correctness = {
  proc main(m:ptext) : bool = {

  var pk : pkey;
  var sk : skey;
  var c  : ctext;
  var m' : ptext option;

    (pk, sk) <- ElGamal.keygen();
    c = ElGamal.encrypt(pk, m);
    m'= ElGamal.decrypt(sk, c);

    return (m' = Some m);
    }
}.

local lemma ElGamal_correct &m m : 
    Pr[Correctness.main(m) @ &m : res] = 1%r.
  proof. 
    byphoare. conseq (: _ ==> true) (: _ ==> res). progress.
    proc. inline*. swap 5 -1. wp. rnd. wp. rnd. skip. progress.
    rewrite pow_pow pow_pow. rewrite mulC. rewrite mulA.  
    rewrite mul_pow. have -> : g ^ (y0 * -sk0 + sk0 * y0) = g1.
    smt. rewrite mul1. trivial. proc. inline*. 
    swap 5 -1. wp. rnd. wp. rnd. skip. progress.
    smt. smt. trivial. trivial. 
qed.    
end section Correctness.

                (* 6. Security section *)

section Security.

(* Prove that for all adversaries A, we have
   |Pr[CPA(ElGamal, A).main() @ &m : res] - 1%r/2%r| =
  |Pr[DDH0(DDHAdv(A).main() @ &m : res] -
  Pr[DDH1(DDHAdv(A).main() @ &m : res]| *)

declare module A:Adversary.
axiom AchooseLL : islossless A.choose.
axiom AguessLL  : islossless A.guess.

(* 6.1 |Pr[CPA(ElGamal, A).main() @ &m : res]| =
  |Pr[DDH0(DDHAdv(A)).main() @ &m : res]| *)

local lemma CPA_DDH0 &m :
  Pr[CPA(ElGamal, A).main() @ &m : res] =
  Pr[DDH0(DDHAdv(A)).main() @ &m : res].
    proof.
      byequiv. proc*. inline*. wp. call(_:true). wp. auto.
      swap{1} 7 -5. auto. call(_:true). auto. progress. 
      rewrite pow_pow. trivial. smt. trivial. trivial.
  qed.


      (* 6.2 Create a module that truly guesses *)
      
  local module Random = {
    proc main() : bool = {
    var x, y, z, m0, m1, b, b';
    x <$ FDistr.dt;
    y <$ FDistr.dt;
    (m0, m1) <- A.choose(g^x);
    z <$ FDistr.dt;
    b' <- A.guess(g^y, g^z);
    b <$ {0,1};
    return b' = b;
      }
    }.

(* 6.3 Show that the probability of DDH1 to guess right is equal 
to the probability of the Random module to guess right. *)

local lemma DDH1_random &m :
    Pr[DDH1(DDHAdv(A)).main() @ &m : res] =
    Pr[Random.main() @ &m : res].
    proof.
        byequiv. proc. inline*. swap{1} 3 2. swap{1} [5..6] 2.
        swap{2} 6 -2. auto. call(_:true). wp.
        rnd (fun z, z + log (if b then m1 else m0){2}) 
        (fun z, z - log (if b then m1 else m0){2}).
        auto. call(_:true). auto. progress. smt. smt. 
        smt. smt. smt. trivial. trivial.
      qed.

(* 6.4 Show that the probability of the Random module to guess 
right is a half *)

local lemma random_half &m :
    Pr[Random.main() @ &m : res] = 1%r / 2%r.
    proof.
        byphoare => //. proc. rnd (pred1 b'). progress.
        conseq(:_==>true). progress. smt.
        have -> : pred1 b' v. assumption. trivial.
        call AguessLL. auto. call AchooseLL. auto. 
        progress. smt. 
    qed.
    
(* 6.5 Connecting the lemmas to prove the advantage of ElGamal *)

local lemma finished &m :
    Pr[CPA(ElGamal, A).main() @ &m : res] - 1%r/2%r = 
    Pr[DDH0(DDHAdv(A)).main() @ &m : res] -
    Pr[DDH1(DDHAdv(A)).main() @ &m : res].
    proof. 
        rewrite (DDH1_random &m). rewrite (random_half &m).
        rewrite (CPA_DDH0 &m). trivial.
    qed.

print finished.
end section Security.
}.