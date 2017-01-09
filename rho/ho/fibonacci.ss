/*
  Inspired by Fibonacci example in Cilk-5.4.6 Reference Manual
  supertech.csail.mit.edu/cilk/manual-5.4.6.pdf

  Demonstrate the use of FORK on recursive procedures,
  which is handled in the same way as that of non-recursive
  procedures.

 */

relation fiba(int n, int f).
axiom n=0 ==> fiba(n,0).
axiom n=1 ==> fiba(n,1).
axiom n > 1 & fiba(n-1,f1) & fiba(n-2,f2) ==> fiba(n,f1+f2).

/**************************************/
/******* THREADS **********************/
pred_prim THRD{(-)P,(+)Q}<n:int,result:cell>
inv result!=null;

pred_prim THRD2{(+)Q@Split}<n:int,result:cell>
inv result!=null;

//after join
pred_prim dead<>
inv true;

//normalization of dead threads
lemma "normalize" self::THRD2{%Q}<x,y> * self::dead<> -> %Q;

//this new thread multiplies x and y by 10
thrd create_thrd() // with %P
  requires true
  ensures (exists n,result: res::THRD{result::cell<_> & n>= 0,
                                      result::cell<v> & fiba(n,v)}<n,result>);

void fork_thrd(thrd t,int n, cell result)
  requires t::THRD{%P,%Q}<n,result> * %P
  ensures  t::THRD2{%Q}<n,result>;

void join_thrd(thrd t)
  requires exists n, result: t::THRD2{%Q}<n,result>
  ensures  t::dead<> * %Q;
/**************************************/

data cell{
  int val;
}

void destroyCell(cell c)
  requires c::cell<_>
  ensures emp;

//sequential version
void seq_fib(int n, cell result)
  requires result::cell<_> & n>= 0
  ensures result::cell<v> & fiba(n,v);
{
  if (n <= 1)
    result.val = n;
  else{
    cell result1 = new cell(0);
    cell result2 = new cell(0);
    seq_fib(n-1,result1);
    seq_fib(n-2,result2);
    result.val = result1.val + result2.val;
    destroyCell(result1); destroyCell(result2);
  }
}

//parallel version
void para_fib(int n, cell result)
  requires result::cell<_> & n>= 0
  ensures result::cell<v> & fiba(n,v);
{
  if (n < 10){
    seq_fib(n,result);
  }else{
    cell result1 = new cell(0);
    cell result2 = new cell(0);

    thrd id1 = create_thrd();
    thrd id2 = create_thrd();

    fork_thrd(id1,n-1,result1); //FORK a recursive procedure
    fork_thrd(id2,n-2,result2); //FORK a recursive procedure

    join_thrd(id1);
    join_thrd(id2);

    result.val = result1.val + result2.val;

    destroyCell(result1); destroyCell(result2);

  }
}
