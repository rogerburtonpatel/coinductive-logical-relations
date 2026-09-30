## Up and down the clock tower

A bit of scratch work on using tower induction to replace the step counts in logical relations. 
This replaces `nat` step counts with stages of the tower (the final chain of a monotone function), 
with the new definition of "later" being "strictly higher in the tower" (aka, fewer steps taken).

The development needs some classical trickery as we need the fact that the tower is a chain
along with the fact that it is gap-free, which we prove via (dual) Bourbaki–Witt.
This lets us do 'the trick,' which is essentially to use a flavor of Löb induction that takes this new definition of "later" expressed via the tower. 
This 'clock tower' approach is nice for using tower induction to prove some of the trickier cases for general recursion and sequencing in LRs for languages with nontermination.
Although it is not yet much easier to use than step indexing, it also gives transfinite indices for free via closure under infima 
(here we only use ω+1 but the results hold for ordinals of any size). 
The main cost is a positivity condition on `unfold`, which means you can't unfold negative recursive types. 
I believe this is recoverable by staging `Mu`, which will require something more complex than a `gfp`
(a fixed-point construction for a non-monotone (contractive) map). 

This repo builds off of Stephanie Weirich's [Programming Languages: Semantics and Types](https://github.com/sweirich/pl-semantics-and-types) course. 
Many of the proofs are written by an AI programming assistant (Claude Code). 

To use:
```
git clone --recurse-submodules https://github.com/rogerburtonpatel/coinductive-logical-relations.git
cd coinductive-logical-relations
```
If you already cloned without `--recurse-submodules`:

```git submodule update --init```
