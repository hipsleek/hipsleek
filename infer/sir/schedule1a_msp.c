// 14
/*  -*- Last-Edit:  Wed May 7 10:12:52 1993 by Monica; -*- */
/*
Note:
- because of lemma, del_ele and its callers are not corrected
 */

//#include <stdio.h>

/* A job descriptor. */

//#define NULL 0


//#define NEW_JOB        1
//#define UPGRADE_PRIO   2
//#define BLOCK          3
//#define UNBLOCK        4
//#define QUANTUM_EXPIRE 5
//#define FINISH         6
//#define FLUSH          7

//#define MAXPRIO 3

//typedef struct _job {
//    struct  _job *next, *prev; /* Next and Previous in job list. */
//    int          val  ;         /* Id-value of program. */
//    short        priority;     /* Its priority. */
//} Ele, *Ele_Ptr;

data node {
	int val;
    int priority;
    node next;
}

//typedef struct list		/* doubly linked list */
//{
//  Ele *first;
//  Ele *last;
//  int    mem_count;		/* member count */
//} List;

/* view for a doubly linked list with size, we use ll and lseg */
/*
ll<n> == self=null & n=0
  or self::node<_, _, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
  or self::node<_,_, q> * q::lseg<p, n-1>
	inv n>=0;

lemma self::ll<n> <-> self::lseg<null,n>;
//lemma self::lseg<p,n> * p::node<_,_, q>  -> self::lseg<q,n+1>;
lemma "V1" self::lseg<p,n> & n = a + b & a,b >=0 <-> self::lseg<r,a> * r::lseg<p,b>;
*/
ll1<n> == self=null & n=0
  or self::node<_, prio, q> * q::ll1<n-1> & prio >=1 & prio<=3
	inv n>=0;

lseg1<p, n> == self=p & n=0
  or self::node<_,prio, q> * q::lseg1<p, n-1> & prio >=1 & prio<=3
	inv n>=0;

lemma self::ll1<n> <-> self::lseg1<null,n>;
lemma self::lseg1<p,n> * p::node<_,v2, q> & v2>=1 & v2<=3 -> self::lseg1<q,n+1>;
lemma "V2" self::lseg1<p,n> & n = a + b & a,b >=0 <-> self::lseg1<r,a> * r::lseg1<p,b>;

node get_first1(node x)
  requires x::ll1<n>
  ensures x::ll1<n> & res=x;
{
  return x;
}

node get_first_seg1(node x)
  requires x::lseg1<q,n>
  ensures x::lseg1<q, n> & res=x;
{
  return x;
}

int get_mem_count1(node x)
  requires x::ll1<n>
  ensures  x::ll1<n> & res=n;
/*-----------------------------------------------------------------------------
  new_ele
     alloates a new element with value as num.
-----------------------------------------------------------------------------*/
node new_ele(int new_num)
  requires true
  ensures res::node<new_num, 0,null>;

{
  return new node(new_num, 0, null);
}

/*-----------------------------------------------------------------------------
  new_list
        allocates, initializes and returns a new list.
        Note that if the argument compare() is provided, this list can be
            made into an ordered list. see insert_ele().
-----------------------------------------------------------------------------*/
node new_list()
  requires true
  ensures res=null;

/*-----------------------------------------------------------------------------
  append_ele
        appends the new_ele to the list. If list is null, a new
	list is created. The modified list is returned.
insert at the tail
-----------------------------------------------------------------------------*/
node append_ele1(ref node x, node a, int prio)
  requires x::ll1<n> * a::node<v1,v2,null> & v2=prio & v2>=1 & v2<=3
  ensures x'::lseg1<a,n> * a::node<v1,v2,null> & res=x' & v2>=1 & v2<=3;
/*-----------------------------------------------------------------------------
  find_nth
        fetches the nth element of the list (count starts at 1)
 -----------------------------------------------------------------------------*/
//relation FNH(int a, int b, int c).
node find_nth_helper1(node l, int j)
//infer [FNH]
  requires l::lseg1<p,n> & n>=j & j>=1
  ensures res::lseg1<p,m> * l::lseg1<res,j-1>  & m=n-j+1//FNH(m,n,j)//(m=n-j+1)
  & res!=null;
{
  if (j>1){
    //assume false;
    node r2=find_nth_helper1(l.next, j-1);
    return r2;
  }
  else {
    //assume false;
     return l;
  }
}

node find_nth1(node f_list, int j)
  requires f_list::ll1<n> & n>=j & j>=1
  ensures f_list::lseg1<res,j-1> * res::node<_,prio,q>
  * q::ll1<n-j> & prio>=1 & prio<=3;

relation FIND(int a).
node find_nth2(node f_list, int j)
  infer [FIND]
  requires f_list::ll1<n> & n>=j & j>=1
  ensures f_list::lseg1<res,j-1> * res::node<_,prio,q>
  * q::ll1<n-j> & FIND(prio);//prio>=1 & prio<=3;
{
  node f_ele;

  f_ele = get_first_seg1(f_list);
  f_ele = find_nth_helper1(f_ele,j);
  return f_ele;
}

node find_nth21(node f_list, int j)
  requires  f_list::ll1<n> & j>=1 & n>=1
 case {
  j <= n -> ensures (exists q: f_list::lseg1<res,j-1> * res::node<_,v2,q> * q::ll1<n-j> & v2>=1 & v2<=3);
  j > n -> ensures f_list::ll1<n> & res=null;
}

/* better specs
node find_nth2(node f_list, int j)
  requires j>=1 //& n>=1
 case {
  f_list = null -> ensures f_list=null & res=null;
  f_list != null -> requires f_list::ll<n>
 case {
  j <= n -> ensures (exists q: f_list::lseg<res,j-1> * res::node<_,v2,q> * q::ll<n-j> & v2>=1 & v2<=3);
  j > n -> ensures f_list::ll<n> & res=null;
}
}*/


/*-----------------------------------------------------------------------------
  del_ele
        deletes the old_ele from the list.
        Note: even if list becomes empty after deletion, the list
	      node is not deallocated.
-----------------------------------------------------------------------------*/
node del_ele1(ref node x, ref node ele)
  requires (exists j,q: x::lseg1<ele,j> * ele::node<v1,v2,q> * q::ll1<m> &  v2 >=1 & v2 <= 3) //&  v2 >=1 & v2 <= 3
  ensures x'::lseg1<q,j> * q::ll1<m> * ele'::node<v1,v2,q>& v2 >=1 & v2 <= 3 & res=x';//'

/*-----------------------------------------------------------------------------
   free_ele
       deallocate the ptr. Caution: The ptr should point to an object
       allocated in a single call to malloc.
-----------------------------------------------------------------------------*/
void free_ele(ref node ptr)
  requires ptr::node<_,_,_>
  ensures ptr'= null;//'
{
    ptr = null;
}

global int alloc_proc_num;
global int num_processes;
//Ele* cur_proc;
global node cur_proc;
//List *prio_queue[/*MAXPRIO*/3+1]; 	/* 0th element unused */
global node prio_queue1;
global node prio_queue2;
global node prio_queue3;
//List *block_queue;
global node block_queue;


/*
requires  pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> * cur_proc::ll<n>
case{
  n1+n2+n3 >0 -> ensures pq1'::ll<n4> * pq2'::ll<n5> * pq3'::ll<n6>  & num_processes' = num_processes -1 & n4+n5+n6=n1+n2+n3-1;
  n1+n2+n3 <=0 -> ensures pq1'=null & pq2'=null & pq3'=null  & num_processes' = num_processes;
}
 */
void finish_process(ref node pq1,ref node pq2,ref node pq3, ref node cur_proc, ref int num_processes)
  requires  pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> * cur_proc::ll1<n>
case{
  n3 > 0 ->
     ensures  pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3-1> & cur_proc' = null & num_processes' = num_processes -1;
  n3<=0 -> case {
      n2>0 -> ensures pq1'::ll1<n1> * pq3'::ll1<n3> * pq2'::ll1<n2-1> & cur_proc' = null & num_processes' = num_processes -1;
      n2<=0 -> case{
        n1>0 -> ensures pq3'::ll1<n3> * pq2'::ll1<n2> * pq1'::ll1<n1-1> & cur_proc' = null & num_processes' = num_processes -1;
        n1<=0 -> ensures pq1'=null &  pq2'= null & pq3'= null & cur_proc' = null & num_processes' = num_processes;
      }
    }
}

//17
void finish_process1(ref node pq1,ref node pq2,ref node pq3, ref node cur_proc, ref int num_processes)
  requires  pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> * cur_proc::ll1<n>
case{
  n3 > 0 ->
    ensures  pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3-1>  & cur_proc' = null & num_processes' = num_processes -1;
  n3<=0 -> case {
      n2>0 -> ensures pq1'::ll1<n1> * pq3'::ll1<n3> * pq2'::ll1<n2-1> & cur_proc' = null & num_processes' = num_processes -1;
      n2<=0 -> case{
        n1>0 -> ensures pq3'::ll1<n3> * pq2'::ll1<n2> * pq1'::ll1<n1-1> & cur_proc' = null & num_processes' = num_processes -1;
        n1<=0 -> ensures pq1'=null &  pq2'= null & pq3'= null & cur_proc' = null & num_processes' = num_processes;
      }
    }
}
{
    schedule();
    if (cur_proc != null)
    {
      //fprintf(stdout, "%d ", cur_proc->val);
      free_ele(cur_proc);
      num_processes--;
    }
}
/*more precise specs. need bags predicates
requires pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> * cur_proc::ll<n>
 case{
  n3 > 0 ->
     ensures pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3-1> * cur_proc'::node<_,1,null>;
  n3<=0 -> case {
      n2>0 -> ensures  pq1'::ll<n1> * pq3'::ll<n3> * pq2'::ll<n2-1> * cur_proc'::node<_,2,null>;
      n2<=0 -> case{
        n1>0 -> ensures pq3'::ll<n3> * pq2'::ll<n2> * pq1'::ll<n1-1> * cur_proc'::node<_,3,null>;
        n1<=0 -> ensures pq1'=null &  pq2'= null & pq3'= null & cur_proc' = null;
      }
    }
 }
 requires  pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> * cur_proc::ll<n>
case{
  n1+n2+n3 >0 -> ensures pq1'::ll<n4> * pq2'::ll<n5> * pq3'::ll<n6>* cur_proc'::node<_,_,null> & n4+n5+n6=n1+n2+n3-1;
  n1+n2+n3 <=0 -> ensures pq1'=null & pq2'=null & pq3'=null & cur_proc' = null;
}
 */
void schedule(ref node cur_proc, ref node pq1, ref node pq2,ref node pq3)
 requires pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> * cur_proc::ll1<n>
 case{
  n3 > 0 ->
    ensures pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3-1> * cur_proc'::node<_,v2,null> & v2>=1 & v2<=3;
  n3<=0 -> case {
    n2>0 -> ensures  pq1'::ll1<n1> * pq3'::ll1<n3> * pq2'::ll1<n2-1> * cur_proc'::node<_,v2,null>& v2>=1 & v2<=3;
      n2<=0 -> case{
        n1>0 -> ensures pq3'::ll1<n3> * pq2'::ll1<n2> * pq1'::ll1<n1-1> * cur_proc'::node<_,v2,null> & v2>=1 & v2<=3;
        n1<=0 -> ensures pq1'=null &  pq2'= null & pq3'= null & cur_proc' = null;
      }
    }
 }

relation SCH1(int a).
void schedule1(ref node cur_proc, ref node pq1, ref node pq2,ref node pq3)
//infer @post [SCH1]
 requires pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> * cur_proc::ll1<n>
 case{
  n3 > 0 ->
    ensures pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3-1> * cur_proc'::node<_,v2,null> & v2>=1 & v2<=3;//& SCH1(v2)
  n3<=0 -> case {
      n2>0 -> ensures  pq1'::ll1<n1> * pq3'::ll1<n3> * pq2'::ll1<n2-1> * cur_proc'::node<_,v2,null> & v2>=1 & v2<=3 ;
      n2<=0 -> case{
        n1>0 -> ensures pq3'::ll1<n3> * pq2'::ll1<n2> * pq1'::ll1<n1-1> * cur_proc'::node<_,v2,null> & v2>=1 & v2<=3;
        n1<=0 -> ensures pq1'=null &  pq2'= null & pq3'= null & cur_proc' = null;//SCH1(pq1', pq2',pq3', cur_proc')
      }
    }
 }
{
    int n;
    cur_proc = null;
    n = get_mem_count1(pq3);
    if (n > 0){
      cur_proc = find_nth1(pq3, 1);
      //dprint;
      pq3 = del_ele1(pq3,  cur_proc);
      cur_proc.next = null;
      return;
    }
    n = get_mem_count1(pq2);
    if (n > 0){
      cur_proc = find_nth1(pq2, 1);//get_first_node(prio_queue2);
      pq2 = del_ele1(pq2, cur_proc);
      cur_proc.next = null;
      return;
    }
    n = get_mem_count1(pq1);
    if (n > 0){
      cur_proc = find_nth1(pq1, 1);//get_first(prio_queue1);
      pq1 = del_ele1(pq1,  cur_proc);
      cur_proc.next = null;
      return;
    }
}


void do_upgrade_process_prio(int prio, int ratio, ref node pq1, ref node pq2)
requires pq1::ll1<n1> * pq2::ll1<n2> & ratio >=1 & prio>=1 & prio<=3
  case {
    n1 > 0 ->  case {
      ratio <= n1  -> ensures pq1'::ll1<n1-1> * pq2'::ll1<n2+1>;
      ratio > n1 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2> ;
      }
    n1 <= 0 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2>;//'
}

//4
//relation DUP1(int a, int b).
//relation DUP2(int a, int b).
void do_upgrade_process_prio1(int prio, int ratio, ref node pq1, ref node pq2)
//infer [DUP1,DUP2]
  requires pq1::ll1<n1> * pq2::ll1<n2> & ratio >=1 & prio>=1 & prio<=3
 case {
  n1 > 0 ->  case {
    ratio <= n1  -> ensures pq1'::ll1<n1-1> * pq2'::ll1<n2+1>;
    ratio > n1 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2> ;
  }
  n1 <= 0 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2>;//'
}
{
  int count;
  int n;
  node proc;
  count = get_mem_count1(pq1) ;
  if (count > 0)
    {
      n = ratio;//(int) (count*ratio + 1);
      proc = find_nth21(pq1, n);
      // assume (false);
      if (proc != null) {
        proc.next = null;
        pq1 = del_ele1(pq1, proc);
        proc.priority = prio;
        //dprint;
        // assume (false);
        pq2 = append_ele1(pq2, proc, prio);
        // dprint;
        // assume (false);
      }
      //dprint;
      // assume (false);
    }
}


void upgrade_process_prio(int prio, int ratio, ref node pq1, ref node pq2, ref node pq3)
requires pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> & prio>0 & prio <=3 & ratio >=1
 case {
  prio = 1 -> case {
    n1 > 0 ->  case {
      ratio <= n1  -> ensures pq1'::ll1<n1-1> * pq2'::ll1<n2+1> * pq3'::ll1<n3>;
      ratio > n1 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3>;
      }
    n1 <= 0 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3>;
  }
  prio = 2 -> case {
      n2 > 0 -> case {
      ratio <= n2 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2-1> * pq3'::ll1<n3+1>;
    ratio > n2 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3>;
       }
      n2 <= 0 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3>;
  }
  prio <1 | prio >2 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3>; //'
}
{
    int count;
    int n;
    node proc;
    node src_queue, dest_queue;

       if (prio >= /*MAXPRIO*/3)
         return;
        if (prio == 1) {
          do_upgrade_process_prio(prio, ratio, pq1, pq2);
        }
        else if (prio == 2) {
          do_upgrade_process_prio(prio, ratio, pq2, pq3);
        }
    //    if (prio >= /*MAXPRIO*/3)
    /*     return;
    else if (prio == 1) {
      src_queue =  pq1;
      dest_queue = pq2;
    }else if (prio == 2) {
      src_queue =  pq2;
      dest_queue = pq3;
    }
    count = get_mem_count(src_queue);
    if (count > 0)
      {
        n = ratio;//(int) (count*ratio + 1);
        //dprint;
        // assume (false);
        proc = find_nth2(src_queue, n);
        // assume (false);
        if (proc != null) {
          proc.next = null;
          src_queue = del_ele(src_queue, proc);
          proc.priority = prio;
           dprint;
          // assume (false);
           dest_queue = append_ele(dest_queue, proc);
          //dprint;
           // assume (false);
        }
        // assume (false);
      }
    */
}
/* more precise specs
requires pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> & ratio >=1
  case {
  bq != null -> requires bq::ll<m> & m >0
 case{
    ratio < m -> ensures bq'::ll<m-1> * pq1'::ll<n4> * pq2'::ll<n5> * pq3'::ll<n6> & n4+n5+n6=n1+n2+n3+1;
    ratio = m -> ensures bq'::ll<m-1> * pq1'::ll<n4> * pq2'::ll<n5> * pq3'::ll<n6> & n4+n5+n6=n1+n2+n3+1;
    ratio > m -> ensures bq'::ll<m> * pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3>;
  }
   bq=null -> ensures pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3> & bq'=null;//
 }
 */

void unblock_process(int ratio, ref node bq, ref node pq1, ref node pq2, ref node pq3)
 requires pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> & ratio >=1
  case {
  bq != null -> requires bq::ll1<m> & m >0
 case{
    ratio <= m -> ensures bq'::ll1<m-1> * pq1'::ll1<n4> * pq2'::ll1<n5> * pq3'::ll1<n6> & n4+n5+n6=n1+n2+n3+1;
    ratio > m -> ensures true;
  }
   bq=null -> ensures pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3> & bq'=null;//
 }

//10
//relation UP1(int a, int b, int c, int d, int e, int f).
// relation UP2(int a, int b).
//  relation UP3(node a).
void unblock_process1(int ratio, ref node bq, ref node pq1, ref node pq2, ref node pq3)
//infer [UP1, UP2, UP3]
 requires pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> & ratio >=1
  case {
  bq != null -> requires bq::ll1<m> & m >0
 case{
    ratio <= m -> ensures bq'::ll1<m-1> * pq1'::ll1<n4> * pq2'::ll1<n5> * pq3'::ll1<n6> & n4+n5+n6=n1+n2+n3+1;
    ratio > m -> ensures true;
  }
  bq=null -> ensures pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3> & bq'=null;//
 }

/*
  requires block_queue::ll<n> * pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> & ratio >=1
  case {
  n > 0 -> requires ratio <= n
	ensures block_queue'::ll<n-1> * pq1'::ll<n4> * pq2'::ll<n5> * pq3'::ll<n6> & n4+n5+n6=n1+n2+n3+1;
  n <= 0 -> ensures block_queue'::ll<n> * pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3> ;
  }
*/
{
    int count;
    int n;
    node proc;
    int prio;
    if (bq != null)
    {
      count = get_mem_count1(bq);
      n = ratio;//(int) (count*ratio + 1);
      proc = find_nth21(bq, n);
      if (proc != null) {
	    // block_queue = del_ele(block_queue, proc);
	    /* append to appropriate prio queue */
	    prio = proc.priority;
        if (prio == 1){
          // dprint;
          bq = del_ele1(bq, proc);
          proc.next = null;
          pq1 = append_ele1(pq1, proc, prio);}
        else if (prio == 2){
          bq = del_ele1(bq, proc);
          proc.next = null;
          pq2 = append_ele1(pq2, proc, prio);}
        else if (prio == 3){
          bq = del_ele1(bq, proc);
          proc.next = null;
          pq3 = append_ele1(pq3, proc,prio);}
        //  assume (false);
      }
      //dprint;
      //assume (false);
    }
    // dprint;
    //	assume (false);
}
/*
more precise specs.
requires cur_proc::ll<n> * pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3>
 case {
  n1+n2+n3>0 -> ensures  true;//pq1'::ll<n4> * pq2'::ll<n5> * pq3'::ll<n6> &
  //n4+n5+n6=n1+n2+n3 & cur_proc' != null;
  n1+n2+n3<=0 -> ensures true;//pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3> & cur_proc' = null;
}
 */
//do not infer, sementation fault
relation QE1(int a).
relation QE2(int a).
relation QE3(int a).
void quantum_expire(ref node cur_proc, ref node pq1, ref node pq2, ref node pq3)
/*
  requires cur_proc::ll1<n> * pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3>
 case {
  n1+n2+n3>0 -> ensures  cur_proc'::node<_, v2,_> ;//& v2>=1 & v2<=3;//'
  n1+n2+n3<=0 -> ensures true;
}
*/
/* 6
QE1: v23>=1 & 3>=v23
QE2: v2>=1 & 3>=v2
QE3: v2>=1 & 3>=v2
 */
  infer [QE1,QE2,QE3]
requires pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> * cur_proc::ll1<n>
 case{
  n3 > 0 ->
    ensures  cur_proc'::node<_,v23,null> & QE1(v23);//& v2>=1 & v2<=3;//'
  n3<=0 -> case {
    n2>0 -> ensures cur_proc'::node<_,v2,null> & QE2(v2);//v2>=1 & v2<=3;//'
      n2<=0 -> case{
        n1>0 -> ensures cur_proc'::node<_,v2,null> & QE3(v2);//v2>=1 & v2<=3;//'
        n1<=0 -> ensures pq1'=null &  pq2'= null & pq3'= null & cur_proc' = null;
      }
    }
 }
{
    int prio;
    schedule(cur_proc, pq1, pq2,pq3);
    if (cur_proc != null)
    {
      //dprint;
      //assert (cur_proc.priority=4);
      prio = cur_proc.priority;
      //assert (prio=4);
       if (prio == 1)
         pq1 = append_ele1(pq1, cur_proc, prio);
        if (prio == 2)
          pq2 = append_ele1(pq2, cur_proc, prio);
        if (prio == 3)
          pq3 = append_ele1(pq3, cur_proc, prio);
    }
}

/*void block_process(ref node cur_proc, ref node block_queue, ref node pq1, ref node pq2, ref node pq3)*/
/*  requires cur_proc::ll1<n> * block_queue::ll1<n> * pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3>*/
/*case {*/
/*  n1+n2+n3 > 0 -> ensures block_queue'::ll1<n+1> * pq1'::ll1<n4> * pq2'::ll1<n5> * pq3'::ll1<n6> & cur_proc'!=null&*/
/*   n1+n2+n3=n4+n5+n6+1;*/
/*   n1+n2+n3 <= 0 -> ensures block_queue'::ll1<n> * pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3> &*/
/*        cur_proc' = null;*/
/*}*/

void block_process1(ref node cur_proc, ref node block_queue, ref node pq1, ref node pq2, ref node pq3)
//  infer [BP1]
/*
  requires cur_proc::ll1<n> * block_queue::ll1<n> * pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3>
case {
  n1+n2+n3 > 0 -> ensures block_queue'::ll1<n+1> * pq1'::ll1<n4> * pq2'::ll1<n5> * pq3'::ll1<n6> & cur_proc'!=null&
   n1+n2+n3=n4+n5+n6+1;
   n1+n2+n3 <= 0 -> ensures block_queue'::ll1<n> * pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3> &
        cur_proc' = null;
}
*/
  requires cur_proc::ll1<n> * block_queue::ll1<n> * pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3>
case{
  n3 > 0 ->
    ensures  block_queue'::lseg1<cur_proc',n> * pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3-1> * cur_proc'::node<_,v2,null>
   & v2>=1 & v2<=3;//' & BP1(v2);
  n3<=0 -> case {
    n2>0 -> ensures block_queue'::lseg1<cur_proc',n+1> * pq1'::ll1<n1> * pq2'::ll1<n2-1> * pq3'::ll1<n3>* cur_proc'::node<_,v2,null>& v2>=1 & v2<=3;//'
      n2<=0 -> case{
        n1>0 -> ensures block_queue'::lseg1<cur_proc',n> * pq1'::ll1<n1-1> * pq2'::ll1<n2> * pq3'::ll1<n3>* cur_proc'::node<_,v2,null> & v2>=1 & v2<=3;//'
        n1<=0 -> ensures block_queue'::ll1<n> & pq1'=null &  pq2'= null & pq3'= null & cur_proc' = null;//'
      }
    }
 }

//15
relation BP1(int a).
relation BP2(int a).
relation BP3(int a).
void block_process(ref node cur_proc, ref node block_queue, ref node pq1, ref node pq2, ref node pq3)
  infer [BP1,BP2,BP3,n]
/*
  requires cur_proc::ll1<n> * block_queue::ll1<n> * pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3>
case {
  n1+n2+n3 > 0 -> ensures block_queue'::ll1<n+1> * pq1'::ll1<n4> * pq2'::ll1<n5> * pq3'::ll1<n6> & cur_proc'!=null&
   n1+n2+n3=n4+n5+n6+1;
   n1+n2+n3 <= 0 -> ensures block_queue'::ll1<n> * pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3> &
        cur_proc' = null;
}
*/
  requires cur_proc::ll1<n> * block_queue::ll1<n> * pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3>
case{
  n3 > 0 ->
    ensures  block_queue'::lseg1<cur_proc',n> * pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3-1> * cur_proc'::node<_,v2,null>
   & BP1(v2);//& v2>=1 & v2<=3;//' & BP1(v2);
  n3<=0 -> case {
    n2>0 -> ensures block_queue'::lseg1<cur_proc',n+1> * pq1'::ll1<n1> * pq2'::ll1<n2-1> * pq3'::ll1<n3>* cur_proc'::node<_,v2,null> & BP2(v2);//v2>=1 & v2<=3;//'
      n2<=0 -> case{
        n1>0 -> ensures block_queue'::lseg1<cur_proc',n> * pq1'::ll1<n1-1> * pq2'::ll1<n2> * pq3'::ll1<n3>* cur_proc'::node<_,v2,null> & BP3(v2);//& v2>=1 & v2<=3;//'
        n1<=0 -> ensures block_queue'::ll1<n> & pq1'=null &  pq2'= null & pq3'= null & cur_proc' = null;//'
      }
    }
 }

{
    schedule(cur_proc, pq1, pq2,pq3);
    if (cur_proc != null)
    {
      //assert (cur_proc.priority >=1 & cur_proc.priority <=3);
      //dprint;
      //assert(true);
      block_queue = append_ele1(block_queue, cur_proc, cur_proc.priority);
    }
}

node new_process(int prio, ref int alloc_proc_num, ref int num_processes)
  requires prio>0 & prio<=3
  ensures res::node<alloc_proc_num+1, prio, null>
  & (num_processes'= num_processes+1) &
             (alloc_proc_num' = alloc_proc_num+1);

//3
node new_process1(int prio, ref int alloc_proc_num, ref int num_processes)
  requires prio>0 & prio<=3
  ensures res::node<alloc_proc_num+1, prio, null>
  & (num_processes'= num_processes+1) &
             (alloc_proc_num' = alloc_proc_num+1);
{
    node proc;
    alloc_proc_num = alloc_proc_num + 1;
    proc = new_ele(alloc_proc_num);
    proc.priority = prio;
    num_processes++;
    return proc;
}

void add_process(int prio, ref int alloc_proc_num, ref int num_processes, ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> & prio>0 & prio<=3
     case {
    prio = 1 -> ensures  pq1'::ll1<n1+1> * pq2'::ll1<n2> * pq3'::ll1<n3> & (num_processes'= num_processes+1) &
             (alloc_proc_num' = alloc_proc_num+1);
    prio = 2 -> ensures  pq1'::ll1<n1> * pq2'::ll1<n2+1> * pq3'::ll1<n3> & (num_processes'= num_processes+1) &
             (alloc_proc_num' = alloc_proc_num+1);
    prio = 3 -> ensures  pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3+1> & (num_processes'= num_processes+1) &
             (alloc_proc_num' = alloc_proc_num+1);
    prio <= 0 | prio >3 -> ensures pq1'=pq1 & pq2'=pq2 & pq3'=pq3 & (num_processes'= num_processes) &
             (alloc_proc_num' = alloc_proc_num) & flow __error;
 }

//24
void add_process1(int prio, ref int alloc_proc_num, ref int num_processes, ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> & prio>0 & prio<=3
     case {
    prio = 1 -> ensures  pq1'::ll1<n1+1> * pq2'::ll1<n2> * pq3'::ll1<n3> & (num_processes'= num_processes+1) &
             (alloc_proc_num' = alloc_proc_num+1);
    prio = 2 -> ensures  pq1'::ll1<n1> * pq2'::ll1<n2+1> * pq3'::ll1<n3> & (num_processes'= num_processes+1) &
             (alloc_proc_num' = alloc_proc_num+1);
    prio = 3 -> ensures  pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<n3+1> & (num_processes'= num_processes+1) &
             (alloc_proc_num' = alloc_proc_num+1);
    prio <= 0 | prio >3 -> ensures pq1'=pq1 & pq2'=pq2 & pq3'=pq3 & (num_processes'= num_processes) &
             (alloc_proc_num' = alloc_proc_num) & flow __error;
 }
{
    node proc;
    if (prio == 1){
       proc = new_process(prio,alloc_proc_num, num_processes);
       pq1 = append_ele1(pq1, proc, proc.priority);
    }
    if (prio == 2){
      proc = new_process(prio,alloc_proc_num, num_processes);
      pq2 = append_ele1(pq2, proc, proc.priority);
    }
    if (prio == 3){
       proc = new_process(prio,alloc_proc_num, num_processes);
       pq3 = append_ele1(pq3, proc, proc.priority);
    }
    // prio_queue[prio] = append_ele(prio_queue[prio], proc);
    //assume false;
}


node init_prio_queue_helper(node queue,int prio,int i,int n/*, ref int alloc_proc_num, ref int num_processes*/)
  requires queue::ll1<i> & prio>0 & prio<=3 & n >= 0 & i<=n
        ensures res::ll1<n>;
    //&(num_processes'= n) & (alloc_proc_num' = n);//'

//2
node init_prio_queue_helper1(node queue,int prio,int i,int n/*, ref int alloc_proc_num, ref int num_processes*/)
   requires queue::ll1<i> & prio>0 & prio<=3 & n >= 0 & i<=n
        ensures res::ll1<n>;
{
  node proc;
  if (i >= n) return queue;
  proc = new_process(prio, alloc_proc_num, num_processes);
  queue = append_ele1(queue, proc,prio);
  i = i+1;
  return init_prio_queue_helper(queue, prio, i, n);
}

void init_prio_queue(int prio, int num_proc, ref node pq1, ref node pq2, ref node pq3)
  /*ref int alloc_proc_num, ref int num_processes,*/
   requires pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> & prio>0 & prio<=3 & num_proc>=0
  case {
  prio = 1 -> ensures pq1'::ll1<num_proc> * pq2'::ll1<n2> * pq3'::ll1<n3> ;
         //& (num_processes'= num_processes+num_proc) & (alloc_proc_num' = alloc_proc_num+num_proc);
  prio = 2 -> ensures pq1'::ll1<n1> * pq2'::ll1<num_proc> * pq3'::ll1<n3> ;
         //& (num_processes'= num_processes+num_proc) &  (alloc_proc_num' = alloc_proc_num+num_proc);
  prio = 3 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<num_proc> ;
         //& (num_processes'= num_processes+num_proc) & (alloc_proc_num' = alloc_proc_num+num_proc);
  prio <= 0 | prio >3 -> ensures true;
        //(num_processes'= num_processes) & (alloc_proc_num' = alloc_proc_num);//'
}

//21
 relation IPQ3(int a, int b, int c, int d, int e1, int e2, int f).
void init_prio_queue1(int prio, int num_proc, ref node pq1, ref node pq2, ref node pq3)
requires pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> & prio>0 & prio<=3 & num_proc>=0
  case {
  prio = 1 -> ensures pq1'::ll1<num_proc> * pq2'::ll1<n2> * pq3'::ll1<n3> ;
         //& (num_processes'= num_processes+num_proc) & (alloc_proc_num' = alloc_proc_num+num_proc);
  prio = 2 -> ensures pq1'::ll1<n1> * pq2'::ll1<num_proc> * pq3'::ll1<n3> ;
         //& (num_processes'= num_processes+num_proc) &  (alloc_proc_num' = alloc_proc_num+num_proc);
  prio = 3 -> ensures pq1'::ll1<n1> * pq2'::ll1<n2> * pq3'::ll1<num_proc> ;
         //& (num_processes'= num_processes+num_proc) & (alloc_proc_num' = alloc_proc_num+num_proc);
  prio <= 0 | prio >3 -> ensures true;
        //(num_processes'= num_processes) & (alloc_proc_num' = alloc_proc_num);//'
}
{
    node queue = null;
    int i;

    //queue = new_list();
    /*for (i=0; i<num_proc; i++)
    {
	proc = new_process(prio);
	queue = append_ele(queue, proc);
    }*/
    i = 0;
    queue = init_prio_queue_helper(queue, prio, i, num_proc);
     if (prio == 1)
      pq1 = queue;
    if (prio == 2)
      pq2 = queue;
    if (prio == 3)
      pq3 = queue;
    //   prio_queue[prio] = queue;
}

void initialize()
  requires true
  ensures alloc_proc_num' = 0 & num_processes' = 0;
{
    alloc_proc_num = 0;
    num_processes = 0;
}

void main_helper(int i, int maxprio, ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> & i >= 0 & i <= maxprio & maxprio = 3
  ensures (exists n4,n5,n6: pq1'::ll1<n4> * pq2'::ll1<n5> * pq3'::ll1<n6>);//'
{
  if (i>=1){
    init_prio_queue(i, 7, pq1, pq2, pq3);
    i = i -1;
    main_helper(i, maxprio, pq1, pq2, pq3);
  }
}

void main(int argc)
  requires prio_queue1::ll1<n1> * prio_queue2::ll1<n2> * prio_queue3::ll1<n3>
  ensures true;
{
    int command;
    int prio;
//    float ratio;
//    int status;

//    if (argc < (/*MAXPRIO*/3+1))
//    {
//	fprintf(stdout, "incorrect usage\n");
//	return;
//    }
    
      initialize();
//    for (prio=/*MAXPRIO*/; prio >= 1; prio--)
//    {
      prio = 3;
      main_helper(prio, 3, prio_queue1, prio_queue2, prio_queue3);
//    }
//    for (status = fscanf(stdin, "%d", &command);
//	 ((status!=EOF) && status);
//	 status = fscanf(stdin, "%d", &command))
//    {
//	switch(command)
//	{
//	case /*FINISH*/6:
//	    finish_process();
//	    break;
//	case /*BLOCK*/3:
//	    block_process();
//	    break;
//	case /*QUANTUM_EXPIRE*/5:
//	    quantum_expire();
//	    break;
//	case /*UNBLOCK*/4:
//	    fscanf(stdin, "%f", &ratio);
//	    unblock_process(ratio);
//	    break;
//	case /*UPGRADE_PRIO*/2:
//	    fscanf(stdin, "%d", &prio);
//	    fscanf(stdin, "%f", &ratio);
//	    if (prio > /*MAXPRIO*/ || prio <= 0) { 
//		fprintf(stdout, "** invalid priority\n");
//		return;
//	    }
//	    else 
//		upgrade_process_prio(prio, ratio);
//	    break;
//	case /*NEW_JOB*/1:
//	    fscanf(stdin, "%d", &prio);
//	    if (prio > /*MAXPRIO*/3 || prio <= 0) {
//		fprintf(stdout, "** invalid priority\n");
//		return;
//	    }
//	    else 
//		add_process(prio);
//	    break;
//	case /*FLUSH*/7:
//	    finish_all_processes();
//	    break;
//	}
//    }
}


/* A simple input spec:
  
  a.out n3 n2 n1

  where n3, n2, n1 are non-negative integers indicating the number of
  initial processes at priority 3, 2, and 1, respectively.

  The input file is a list of commands of the following kinds:
   (For simplicity, comamnd names are integers (NOT strings)
    
  FINISH            ;; this exits the current process (printing its number)
  NEW_JOB priority  ;; this adds a new process at specified priority
  BLOCK             ;; this adds the current process to the blocked queue
  QUANTUM_EXPIRE    ;; this puts the current process at the end
                    ;;      of its prioqueue
  UNBLOCK ratio     ;; this unblocks a process from the blocked queue
                    ;;     and ratio is used to determine which one

  UPGRADE_PRIO small-priority ratio ;; this promotes a process from
                    ;; the small-priority queue to the next higher priority
                    ;;     and ratio is used to determine which process
 
  FLUSH	            ;; causes all the processes from the prio queues to
                    ;;    exit the system in their priority order

where
 NEW_JOB        1
 UPGRADE_PRIO   2 
 BLOCK          3
 UNBLOCK        4  
 QUANTUM_EXPIRE 5
 FINISH         6
 FLUSH          7
and priority is in        1..3
and small-priority is in  1..2
and ratio is in           0.0..1.0

 The output is a list of numbers indicating the order in which
 processes exit from the system.   

*/


