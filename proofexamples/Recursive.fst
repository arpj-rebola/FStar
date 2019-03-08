module Trivial

let f (x:nat) = x + 1

let lemma_f_pos ()
: Lemma(forall (n:nat). f n > 0)
= ()


let lemma_f_pos ()
: Lemma(forall (n:nat). f n > 0)
= assert (...);
  forall x. x > 0;
  cut (...);
  true
