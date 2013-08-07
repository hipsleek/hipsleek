/*  -*- Last-Edit:  Wed May 7 10:12:52 1993 by Monica; -*- */


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
ll<n> == self=null & n=0
  or self::node<_, _, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
  or self::node<_,_, q> * q::lseg<p, n-1>
	inv n>=0;

lemma self::ll<n> <-> self::lseg<null,n>;
//lemma self::lseg<p,n> * p::node<_,_, q>  -> self::lseg<q,n+1>;
lemma "V1" self::lseg<p,n> & n = a + b & a,b >=0 <-> self::lseg<r,a> * r::lseg<p,b>;

node get_first(node x)
  requires x::ll<n>
  ensures x::ll<n> & res=x;
{
  return x;
}

node get_first_seg(node x)
  requires x::lseg<q,n>
  ensures x::lseg<q, n> & res=x;
{
  return x;
}

int get_mem_count(node x)
  requires x::ll<n>
  ensures  x::ll<n> & res=n;

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
node append_ele(ref node x, node a, int prio)
  requires x::ll<n> * a::node<v1,v2,null> & v2=prio
  ensures x'::lseg<a,n> * a::node<v1,v2,null> & res=x';

/*-----------------------------------------------------------------------------
  find_nth
        fetches the nth element of the list (count starts at 1)
 -----------------------------------------------------------------------------*/
node find_nth_helper(node l, int j)
  requires l::lseg<p,n> & n>=j & j>=1
  ensures res::lseg<p,m> * l::lseg<res,j-1>  & (m=n-j+1)
  & res!=null;
{
  if (j>1){
    //assume false;
    node r2=find_nth_helper(l.next, j-1);
    return r2;
  }
  else {
    //assume false;
     return l;
  }
}

node find_nth(node f_list, int j)
  requires f_list::ll<n> & n>=j & j>=1
  ensures f_list::lseg<res,j-1> * res::node<_,_,q>
           * q::ll<n-j>;
{
  node f_ele;

  f_ele = get_first_seg(f_list);
  f_ele = find_nth_helper(f_ele,j);
  return f_ele;
}

node find_nth2(node f_list, int j)
  requires  f_list::ll<n> & j>=1 & n>=1
 case {
  j <= n -> ensures (exists q: f_list::lseg<res,j-1> * res::node<_,v2,q> * q::ll<n-j> & v2>=1 & v2<=3);
  j > n -> ensures f_list::ll<n> & res=null;
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
node del_ele(ref node x, node ele)
  requires (exists j,q: x::lseg<ele,j> * ele::node<v1,v2,q> * q::ll<m>) //&  v2 >=1 & v2 <= 3
  ensures x'::lseg<q,j> * q::ll<m> * ele::node<v1,v2,q>& v2 >=1 & v2 <= 3 & res=x';//'

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

void finish_process(ref node pq1,ref node pq2,ref node pq3, ref node cur_proc, ref int num_processes)
  requires  pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> * cur_proc::ll<n>
case{
  n3 > 0 ->
     ensures  pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3-1> & cur_proc' = null & num_processes' = num_processes -1;
  n3<=0 -> case {
      n2>0 -> ensures pq1'::ll<n1> * pq3'::ll<n3> * pq2'::ll<n2-1> & cur_proc' = null & num_processes' = num_processes -1;
      n2<=0 -> case{
        n1>0 -> ensures pq3'::ll<n3> * pq2'::ll<n2> * pq1'::ll<n1-1> & cur_proc' = null & num_processes' = num_processes -1;
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
 */
void schedule(ref node cur_proc, ref node pq1, ref node pq2,ref node pq3)
  requires pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> * cur_proc::ll<n>
 case{
  n3 > 0 ->
     ensures pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3-1> * cur_proc'::node<_,_,null>;
  n3<=0 -> case {
      n2>0 -> ensures  pq1'::ll<n1> * pq3'::ll<n3> * pq2'::ll<n2-1> * cur_proc'::node<_,_,null>;
      n2<=0 -> case{
        n1>0 -> ensures pq3'::ll<n3> * pq2'::ll<n2> * pq1'::ll<n1-1> * cur_proc'::node<_,_,null>;
        n1<=0 -> ensures pq1'=null &  pq2'= null & pq3'= null & cur_proc' = null;
      }
    }
 }
{
    int n;
    cur_proc = null;
    n = get_mem_count(pq3);
    if (n > 0){
      cur_proc = find_nth(pq3, 1);
      cur_proc.next = null;
      //dprint;
      pq3 = del_ele(pq3,  cur_proc);
      return;
    }
    n = get_mem_count(pq2);
    if (n > 0){
      cur_proc = find_nth(pq2, 1);//get_first_node(prio_queue2);
      cur_proc.next = null;
      pq2 = del_ele(pq2, cur_proc);
      return;
    }
    n = get_mem_count(pq1);
    if (n > 0){
      cur_proc = find_nth(pq1, 1);//get_first(prio_queue1);
      cur_proc.next = null;
      pq1 = del_ele(pq1,  cur_proc);
      return;
    }
}


void do_upgrade_process_prio(int prio, int ratio, ref node pq1, ref node pq2)
requires pq1::ll<n1> * pq2::ll<n2> & ratio >=1
  case {
    n1 > 0 ->  case {
      ratio <= n1  -> ensures pq1'::ll<n1-1> * pq2'::ll<n2+1>;
      ratio > n1 -> ensures pq1'::ll<n1> * pq2'::ll<n2> ;
      }
    n1 <= 0 -> ensures pq1'::ll<n1> * pq2'::ll<n2>;//'
  }
{
  int count;
  int n;
  node proc;
  count = get_mem_count(pq1) ;
  if (count > 0)
    {
      n = ratio;//(int) (count*ratio + 1);
      proc = find_nth2(pq1, n);
      // assume (false);
      if (proc != null) {
        proc.next = null;
        pq1 = del_ele(pq1, proc);
        proc.priority = prio;
        //dprint;
        // assume (false);
        pq2 = append_ele(pq2, proc, prio);
        // dprint;
        // assume (false);
      }
      //dprint;
      // assume (false);
    }
}
void upgrade_process_prio(int prio, int ratio, ref node pq1, ref node pq2, ref node pq3)
requires pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> & prio>0 & prio <=3 & ratio >=1
 case {
  prio = 1 -> case {
    n1 > 0 ->  case {
      ratio <= n1  -> ensures pq1'::ll<n1-1> * pq2'::ll<n2+1> * pq3'::ll<n3>;
      ratio > n1 -> ensures pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3>; 
      }
    n1 <= 0 -> ensures pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3>;
  }
  prio = 2 -> case {
      n2 > 0 -> case {
      ratio <= n2 -> ensures pq1'::ll<n1> * pq2'::ll<n2-1> * pq3'::ll<n3+1>;
    ratio > n2 -> ensures pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3>;
       }
      n2 <= 0 -> ensures pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3>;
  }
  prio <1 | prio >2 -> ensures pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3>; //'
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
 requires pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> & ratio >=1
  case {
  bq != null -> requires bq::ll<m> & m >0
 case{
    ratio < m -> ensures true;
    ratio = m -> ensures bq'::ll<m-1> * pq1'::ll<n4> * pq2'::ll<n5> * pq3'::ll<n6> & n4+n5+n6=n1+n2+n3+1;
    ratio > m -> ensures true;
  }
   bq=null -> ensures pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3> & bq'=null;//
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
      count = get_mem_count(bq);
      n = ratio + 1;//(int) (count*ratio + 1);
      if (n == (count+1)) n = count;
      proc = find_nth2(bq, n);
      if (proc != null) {
	    // block_queue = del_ele(block_queue, proc);
	    /* append to appropriate prio queue */
	    prio = proc.priority;
        if (prio == 1){
          // dprint;
          bq = del_ele(bq, proc);
          proc.next = null;
          pq1 = append_ele(pq1, proc, prio);}
        else if (prio == 2){
          bq = del_ele(bq, proc);
          proc.next = null;
          pq2 = append_ele(pq2, proc, prio);}
        else if (prio == 3){
          bq = del_ele(bq, proc);
          proc.next = null;
          pq3 = append_ele(pq3, proc, prio);}
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
void quantum_expire(ref node cur_proc, ref node pq1, ref node pq2, ref node pq3)
  requires cur_proc::ll<n> * pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3>
 case {
  n1+n2+n3>0 -> ensures  true;
  n1+n2+n3<=0 -> ensures true;
}
{
    int prio;
    schedule(cur_proc, pq1, pq2,pq3);
    if (cur_proc != null)
    {
      prio = cur_proc.priority;
       if (prio == 1)
          pq1 = append_ele(pq1, cur_proc, prio);
        if (prio == 2)
          pq2 = append_ele(pq2, cur_proc, prio);
        if (prio == 3)
          pq3 = append_ele(pq3, cur_proc, prio);
    }
}

void block_process(ref node cur_proc, ref node block_queue, ref node pq1, ref node pq2, ref node pq3)
  requires cur_proc::ll<n> * block_queue::ll<n> * pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3>
case {
  n1+n2+n3 > 0 -> ensures block_queue'::ll<n+1> * pq1'::ll<n4> * pq2'::ll<n5> * pq3'::ll<n6> &
                           n1+n2+n3=n4+n5+n6+1 & cur_proc'!=null;
   n1+n2+n3 <= 0 -> ensures block_queue'::ll<n> * pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3> & cur_proc' = null;
    }
{
    schedule(cur_proc, pq1, pq2,pq3);
    if (cur_proc != null)
    {
      //dprint;
      block_queue = append_ele(block_queue, cur_proc, cur_proc.priority);
    }
}

node new_process(int prio, ref int alloc_proc_num, ref int num_processes)
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
  requires pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> & prio>0 & prio<=3
     case {
    prio = 1 -> ensures  pq1'::ll<n1+1> * pq2'::ll<n2> * pq3'::ll<n3> & (num_processes'= num_processes+1) &
             (alloc_proc_num' = alloc_proc_num+1);
    prio = 2 -> ensures  pq1'::ll<n1> * pq2'::ll<n2+1> * pq3'::ll<n3> & (num_processes'= num_processes+1) &
             (alloc_proc_num' = alloc_proc_num+1);
    prio = 3 -> ensures  pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<n3+1> & (num_processes'= num_processes+1) &
             (alloc_proc_num' = alloc_proc_num+1);
    prio <= 0 | prio >3 -> ensures pq1'=pq1 & pq2'=pq2 & pq3'=pq3 & (num_processes'= num_processes) &
             (alloc_proc_num' = alloc_proc_num) & flow __Error;
 }
{
    node proc;
    if (prio == 1){
       proc = new_process(prio,alloc_proc_num, num_processes);
       pq1 = append_ele(pq1, proc, proc.priority);
    }
    if (prio == 2){
      proc = new_process(prio,alloc_proc_num, num_processes);
      pq2 = append_ele(pq2, proc,proc.priority);
    }
    if (prio == 3){
       proc = new_process(prio,alloc_proc_num, num_processes);
       pq3 = append_ele(pq3, proc,proc.priority);
    }
    // prio_queue[prio] = append_ele(prio_queue[prio], proc);
}

node init_prio_queue_helper(node queue,int prio,int i,int n/*, ref int alloc_proc_num, ref int num_processes*/)
      requires queue::ll<i> & prio>0 & prio<=3 & n >= 0 & i<=n
  ensures res::ll<n> ;
    //&(num_processes'= n) & (alloc_proc_num' = n);//'
{
  node proc;
  if (i >= n) return queue;
  proc = new_process(prio, alloc_proc_num, num_processes);
  queue = append_ele(queue, proc,prio);
  i = i+1;
  return init_prio_queue_helper(queue, prio, i, n);
}

void init_prio_queue(int prio, int num_proc, ref node pq1, ref node pq2, ref node pq3)
  /*ref int alloc_proc_num, ref int num_processes,*/
   requires pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> & prio>0 & prio<=3 & num_proc>=0
  case {
  prio = 1 -> ensures pq1'::ll<num_proc> * pq2'::ll<n2> * pq3'::ll<n3> ;
         //& (num_processes'= num_processes+num_proc) & (alloc_proc_num' = alloc_proc_num+num_proc);
  prio = 2 -> ensures pq1'::ll<n1> * pq2'::ll<num_proc> * pq3'::ll<n3> ;
         //& (num_processes'= num_processes+num_proc) &  (alloc_proc_num' = alloc_proc_num+num_proc);
  prio = 3 -> ensures pq1'::ll<n1> * pq2'::ll<n2> * pq3'::ll<num_proc> ;
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
  requires pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> & i >= 0 & i <= maxprio & maxprio = 3
  ensures (exists n4,n5,n6: pq1'::ll<n4> * pq2'::ll<n5> * pq3'::ll<n6>);//'
{
  if (i>=1){
    init_prio_queue(i, 7, pq1, pq2, pq3);
    i = i -1;
    main_helper(i, maxprio, pq1, pq2, pq3);
  }
}

void main(int argc)
  requires prio_queue1::ll<n1> * prio_queue2::ll<n2> * prio_queue3::ll<n3>
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


