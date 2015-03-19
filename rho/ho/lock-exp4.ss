/*

  Deadlock due to unordered locking

  WAIT <S |-> l > is represented as a built-in
  prim_pred WAITS<G,S,d>

  //normalization lemma
  lemma "set_comp" self::WAITS<G,S,d> & concrete(S) -> emp & set_comp(G,S,d);

  set_comp(G,S,d) will be translated under the hook

 */

class lck extends Object {}

//Thread: initial state 
pred_prim THRD{(-)P,(+)Q}<l1:lck,l2:lck,ls:LockSet,g:WAIT>;

//Thread: forked state
pred_prim THRD2{(+)Q@Split}<l1:lck,l2:lck,ls:LockSet,g:WAIT>;

//Thread: dead state
pred_prim DEAD<>;

//Lock: initial state 
pred_prim Lock{(+)P}<>;
pred_prim Held{(-)P}<>;
pred_prim Unheld<>;

pred_prim LockSet<S:bag(lck)>;

lemma_split "frac-lock-split" self::Lock{%PP}(f)<> & f=f1+f2 & f1>0.0 & f2>0.0  -> self::Lock{%PP}(f1)<> * self::Lock{%PP}(f2)<> & 0.0<f<=1.0;

lemma "frac-lock-combine" self::Lock{%PPP}(f1)<> * self::Lock{%PPP}(f2)<> -> self::Lock{%PPP}(f1+f2)<>;

lemma "error1" self::Held{%PPPP}<> * self::Unheld<> ->  emp & flow __Fail;


lemma_split "wait-split" self::WAIT<S> -> self::WAIT<S> * self::WAIT<S>;

lemma "wait-combine" self::WAIT<S1> * self::WAIT<S2> -> self::WAIT<S> & S=union(S1,S2);

//normalization of dead threads
lemma "thrd_normalize" self::THRD2{%Q}<l1,l2,ls,g> * self::DEAD<> -> %Q;

lemma "deadlock" self::WAIT<S> & cyclic(S) ->  emp & flow __Fail;

//normalization lemma
lemma "set_comp" self::WAITS<G,S,d> & concrete(S) -> emp & set_comp(G,S,d);



/********************************************/
/****************THREADS*********************/
thrd create_thrd() // with %P
  requires true
  ensures (exists l1,l2,ls,g,S,S1,G,G1: res::THRD{l1::Lock{emp}(0.5)<>@S1 * l2::Lock{emp}(0.5)<>@S1 * ls::LockSet<S> * g::WAIT<G>@S1 & G={} & S={} & l1!=l2,
                                        l1::Lock{emp}(0.5)<> * l2::Lock{emp}(0.5)<> * ls::LockSet<S1> * g::WAIT<G1> & G1={tup2(l1,l2)} & S1={} }<l1,l2,ls,g>);

void fork_thrd(thrd t,lck l1,lck l2, LockSet ls, WAIT g)
  requires t::THRD{%P,%Q}<l1,l2,ls,g> * %P
  ensures  t::THRD2{%Q}<l1,l2,ls,g>;

void join_thrd(thrd t)
  requires exists l1,l2,ls,g: t::THRD2{%Q}<l1,l2,ls,g>
  ensures  t::DEAD<> * %Q;
  requires t::DEAD<>
  ensures  t::DEAD<>;

/********************************************/
/****** LOCKS *******************************/
lck create_lock() // with %P
  requires emp
  ensures res::Lock{emp}<>;

void acquire_lock(lck l, LockSet ls, WAIT g)
  requires l::Lock{%P}(f)<> * ls::LockSet<S> * g::WAIT<G>
  ensures l::Lock{%P}(f)<> * %P * l::Held{%P}<> * ls::LockSet<S1> 
  * g::WAIT<G1> * g::WAITS<G2,S,l> & G1=union(G,G2) & S1=union(S,{l});

void release_lock(lck l,LockSet ls)
  requires l::Held{%P}<> * %P * ls::LockSet<S>
  ensures ls::LockSet<S1> & S1=diff(S,{l});

void dispose_lock(lck l)
  requires l::Lock{%P}<>
  ensures l::Unheld<> * %P;
/********************************************/
/********************************************/

void thread1(lck l1, lck l2, LockSet ls,WAIT g)
  requires l1::Lock{emp}(0.5)<>@S1 * l2::Lock{emp}(0.5)<>@S1 * ls::LockSet<S>
           * g::WAIT<G>@S1 & G={} & S={} & l1!=l2
  ensures l1::Lock{emp}(0.5)<> * l2::Lock{emp}(0.5)<> * ls::LockSet<S1>
  * g::WAIT<G1> & G1={tup2(l1,l2)} & S1={};
{
  acquire_lock(l1,ls,g);
  acquire_lock(l2,ls,g);

  release_lock(l1,ls);
  release_lock(l2,ls);
}

void thread2(lck l1, lck l2, LockSet ls,WAIT g)
  requires l1::Lock{emp}(0.5)<>@S1 * l2::Lock{emp}(0.5)<>@S1 * ls::LockSet<S>
           * g::WAIT<G> & G={} & S={} & l1!=l2
  ensures l1::Lock{emp}(0.5)<> * l2::Lock{emp}(0.5)<> * ls::LockSet<S1>
  * g::WAIT<G1> & G1={tup2(l2,l1)} & S1={};
{
  acquire_lock(l2,ls,g);
  acquire_lock(l1,ls,g);

  release_lock(l1,ls);
  release_lock(l2,ls);
}

// ls for main thread, ls1,ls2 for the two child thread
void main(LockSet ls,LockSet ls1, LockSet ls2,WAIT g)
  requires ls::LockSet<S> * ls1::LockSet<S> * ls2::LockSet<S> * g::WAIT<G> & G={} & S={}
  ensures ls::LockSet<S> * ls1::LockSet<S> * ls2::LockSet<S>  * g::WAIT<G1> & S={};
{
  lck l1 = create_lock();
  lck l2 = create_lock();
  assume l1'!=l2';

  thrd tid =  create_thrd(); //create thread1

  fork_thrd(tid,l1,l2,ls1,g);

  acquire_lock(l2,ls,g);
  acquire_lock(l1,ls,g); // l1 -> l2

  release_lock(l1,ls);
  release_lock(l2,ls);

  join_thrd(tid); // l2 -> l1
  //WAIT{l1 -> l2, l2 -> l1} --> ERROR

  dispose_lock(l1);
  dispose_lock(l2);

}
