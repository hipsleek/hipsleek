

data node {
	int val;
	node next;
}


lseg_one<p> == self = p
	or self::node<_, q> * q::lseg_one<p>
  inv true;

sll_two<> == self = null 
	or self::node<_, q> * q::sll_two<>
  inv true;


bool bool_nondet()
  requires emp & true ensures emp & true;

node new_node()
  requires emp & true ensures res::node<_,_>;

PostPred G(node x, node y).
void create (ref node x)
  requires true ensures x'::lseg_one<x>;//'

//lemma_safe self::sll_two<> <- self::lseg_one<one> & one=null.

lemma_safe self::sll_two<> <- self::lseg_one<q> * q::sll_two<>.

void check (ref node x)
  requires x::sll_two<> ensures x::sll_two<> & x'=x;//'

void main()
{
  node a = null;

  create(a);
  dprint;
  check(a);
}


/*
# ex17z.ss

  Scheduled BaseCaseFold inside lemma application

# ex17.ss (FIXED)

To strip anonymous variables.

!!! **WARNING****astsimp.ml#8758:Post-condition has existentially quantified free vars:[(Anon_14,);(Anon_15,)]
Starting Omega.../usr/local/bin/oc

checkentail (exists a_1655: a'::lseg_one<a_1655>@M&a_1655=null)
 |-  a'::sll_two<>.

 */
