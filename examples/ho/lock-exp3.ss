/*
  WAIT <S |-> l > is represented as a relation waitS<G,S,d>
  waitS<G,S,d> ==translate== {(c,d) | c in S}
 */

class lck extends Object {}

data cell{
  int v;
}

//Lock: initial state 
pred_prim Lock{(+)P}<>;
pred_prim Held{(-)P}<>;
pred_prim Unheld<>;

pred_prim WAITS<b:bag(Object),Object>;

pred_prim LockSet<S:bag(lck)>;

lemma_split "frac-lock-split" self::Lock{%P}(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::Lock{%P}(f1)<> * self::Lock{%P}(f2)<> & 0.0<f<=1.0;

lemma "frac-lock-combine" self::Lock{%P}(f1)<> * self::Lock{%P}(f2)<> -> self::Lock{%P}(f1+f2)<>;

lemma "error1" self::Held{%P}<> * self::Unheld<> ->  emp & flow __Fail;

lck create_lock() // with %P
  requires emp
  ensures res::Lock{emp}<>;

void acquire_lock(lck l, LockSet ls, WAIT g)
  requires l::Lock{%P}(f)<> * ls::LockSet<S> * g::WAIT<G>
  ensures l::Lock{%P}(f)<> * %P * l::Held{%P}<> * ls::LockSet<S1> 
          * g::WAIT<G1> & G1=union(G,G2) & waitS(G2,S,l) & S1=union(S,{l});

void release_lock(lck l,LockSet ls)
  requires l::Held{%P}<> * %P * ls::LockSet<S>
  ensures ls::LockSet<S1> & S1=diff(S,{l});

void dispose_lock(lck l)
  requires l::Lock{%P}<>
  ensures l::Unheld<> * %P;

/* void thread1(lck l1, LockSet ls, WAIT g) */
/*   requires l1::Lock{emp}(f1)<> * ls::LockSet<S> * g::WAIT<G> & S={} & G={} */
/*   ensures l1::Lock{emp}(f1)<> * ls::LockSet<S> * g::WAIT<G> & S={} & G={}; */
/* { */
/*   acquire_lock(l1,ls,g); */
/*   release_lock(l1,ls); */
/* } */

void thread1(lck l1, lck l2, LockSet ls,WAIT g)
  requires l1::Lock{emp}(f1)<> * l2::Lock{emp}(f2)<> * ls::LockSet<S> 
           * g::WAIT<G> & G={} & S={} & l1!=l2
  ensures l1::Lock{emp}(f1)<> * l2::Lock{emp}(f2)<> * ls::LockSet<S1>
  * g::WAIT<G1> & G1={tup2(l1,l2)} & S1={};
{
  acquire_lock(l1,ls,g);
  acquire_lock(l2,ls,g);

  release_lock(l1,ls);
  release_lock(l2,ls);
  dprint;
}

/* void main(LockSet ls) */
/*   requires ls::LockSet<S> & S={} */
/*   ensures ls::LockSet<S> & S={}; */
/* { */
/*   lck x = create_lock(); */

/*   acquire_lock(x,ls); */
/*   release_lock(x,ls); */

/*   acquire_lock(x,ls); */
/*   release_lock(x,ls); */

/*   dispose_lock(x); */

/* } */
