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

data node2 {
	int val;
    int priority;
    node2 prev;
	node2 next;
}

//typedef struct list		/* doubly linked list */
//{
//  Ele *first;
//  Ele *last;
//  int    mem_count;		/* member count */
//} List;

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<_ ,_,p , q> * q::dll<self, n-1> // = q1 
	inv n >= 0;

int get_mem_count(node2 x)
  requires x::dll<_,n>
  ensures res=n;

/*
dll<f,n,l> == self = null & n = 0 & f=null & l=null
  or self::node2<_,_,null,null> & n = 1 & f=self & l=self
  or self::node2<_ ,_ ,p , q> * q::dll<self, n-1> // = q1
	inv n >= 0;
*/
/*-----------------------------------------------------------------------------
  new_ele
     alloates a new element with value as num.
-----------------------------------------------------------------------------*/
/*
Ele* new_ele(new_num) 
int new_num;
{	
    Ele *ele;

    ele =(Ele *)malloc(sizeof(Ele));
    ele->next = NULL;
    ele->prev = NULL;
    ele->val  = new_num;
    return ele;
}
*/
node2 new_ele(new_num)
{
  return new node2(new_num, 0, null, null);
}

/*-----------------------------------------------------------------------------
  new_list
        allocates, initializes and returns a new list.
        Note that if the argument compare() is provided, this list can be
            made into an ordered list. see insert_ele().
            -----------------------------------------------------------------------------*//*
List *new_list()
{
    List *list;

    list = (List *)malloc(sizeof(List));
    
    list->first = NULL;
    list->last  = NULL;
    list->mem_count = 0;
    return (list);
}
                                                                                           */
/*-----------------------------------------------------------------------------
  append_ele
        appends the new_ele to the list. If list is null, a new
	list is created. The modified list is returned.
    -----------------------------------------------------------------------------*//*
List *append_ele(a_list, a_ele)
List *a_list;
Ele  *a_ele;
{
  if (!a_list)
      a_list = new_list();	/* make list without compare function */
/*
  a_ele->prev = a_list->last;	/* insert at the tail */
/*  if (a_list->last)
    a_list->last->next = a_ele;
  else
    a_list->first = a_ele;
  a_list->last = a_ele;
  a_ele->next = NULL;
  a_list->mem_count++;
  return (a_list);
}
*/
node2 append(node2 x, node2 y)

  requires x::dll<q, m> * y::node2<_,_,null,null>
	ensures res::dll<_, m+1>;

{
	node2 tmp;

	if (x == null)
		return y;
	else
	{ 	

		tmp = x.next;
		tmp = append(tmp, y);

		if (tmp != null)
		{
			x.next = tmp; 
			tmp.prev = x;
		}
		else {
			x.next = null;
		}

		return x; 
	}
}
/*-----------------------------------------------------------------------------
  find_nth
        fetches the nth element of the list (count starts at 1)
        -----------------------------------------------------------------------------*//*
Ele *find_nth(f_list, n)
List *f_list;
int   n;
{
    Ele *f_ele;
    int i;

    if (!f_list)
	return NULL;
    f_ele = f_list->first;
    for (i=1; f_ele && (i<n); i++)
	f_ele = f_ele->next;
    return f_ele;
}

                                                                                       */
node2 find_nth_helper(node2 l, int i)
    requires l::dll<p, n> & i<n & n>=0
    ensures res::dll<p,m> & (res=null or i>=n);
{
  if (l = null) return l;
  if (i<n) return find_nth_helper(l.next, i+1);
  else return l;
}

node2 find_nth(node2 f_list, int j)
  requires f_list::dll<p, n> & j<n
  ensures r::node2<_,_,_,q>*q::dll<p,m> & (m = n-j-1) & res=r;
{
  node2 f_ele;
  int i;

  if (f_list == null)
	return null;
  f_ele = f_list;
  f_ele = find_nth_helper(f_list,1);
  return f_ele;
}

node2 get_last(node2 x)
  requires x::dll<p, n> & n>0
  ensures  res::node2(_,_,_,_);
{
  if (n==1) return x;
  else return get_last(x.next);
}

/*-----------------------------------------------------------------------------
  del_ele
        deletes the old_ele from the list.
        Note: even if list becomes empty after deletion, the list
	      node is not deallocated.
-----------------------------------------------------------------------------*/
/*
List *del_ele(d_list, d_ele)
List *d_list;
Ele  *d_ele;
{
    if (!d_list || !d_ele)
	return (NULL);
    
    if (d_ele->next)
	d_ele->next->prev = d_ele->prev;
    else
	d_list->last = d_ele->prev;
    if (d_ele->prev)
	d_ele->prev->next = d_ele->next;
    else
	d_list->first = d_ele->next;
    /* KEEP d_ele's data & pointers intact!! */
/*    d_list->mem_count--;
    return (d_list);
}
*/
node2 del_ele(node2 d_list, node2 d_ele)
   requires x::dll<p, n>
   case d_ele = null -> ensures null;
   case d_ele != null ->{
     case n = 0 -> ensures null;
     case n != 0 -> ensures y::dll<p,n-1>;
 }
{
    if (d_list == null || d_ele == null)
	return (null);

    if (d_ele.next != null){
      node2 tmp = d_ele.next;
      tmp.prev = d_ele.prev;
    }
    else{
      node2 tmp2 = get_last(d_list);
	  tmp2 = d_ele.prev;
    }
    if (d_ele.prev != null){
      node2 tmp3 = d_ele.prev;
      tmp3.next = d_ele.next;
    }
    else
	  d_list = d_ele.next;
    /* KEEP d_ele's data & pointers intact!! */
    //d_list->mem_count--;
    return (d_list);
}

/*-----------------------------------------------------------------------------
   free_ele
       deallocate the ptr. Caution: The ptr should point to an object
       allocated in a single call to malloc.
-----------------------------------------------------------------------------*/
/*void free_ele(ptr)
Ele *ptr;
{
    free(ptr);
}
*/
void free_ele(node2 ptr)
  requires ptr::node<_,_,_,_>
  ensures ptr'=null;//'
{
    ptr = null;
}

int alloc_proc_num;
int num_processes;
//Ele* cur_proc;
node2 cur_proc;
//List *prio_queue[/*MAXPRIO*/3+1]; 	/* 0th element unused */
node2 prio_queue1;
node2 prio_queue2;
node2 prio_queue3;
//List *block_queue;
node2 block_queue;

void
finish_process()
  requires true
 case {cur_proc = null ->  ensures num_processes' = num_processes;//'
  cur_proc != null ->
  ensures num_processes' = num_processes -1;//'
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

void finish_all_processes_helper(int i, int t)
  requires true
  ensures i>=t;
{
  if (i<t){
   finish_process();
   finish_all_processes_helper(i+1, t);
  }
}

void finish_all_processes()
  requires true
  ensures num_processes'=0;//'
{
    int i;
    int total;
    total = num_processes;
    //for (i=0; i<total; i++)
	//finish_process();
    finish_all_processes_helper(0,total);
}

void schedule()
   requires prio_queue1::dll<p1,n1> * prio_queue2::dll<p2,n2> * prio_queue3::dll<p3,n3>
 case{
  n3>0 -> ensures prio_queue1'= prio_queue1 & prio_queue2'=prio_queue2 &
    (exists x, r: prio_queue3::x*r::dll<p,n3-1> & x::node2<_,_,_,_> & prio_queue3'=r & cur_proc' = x);
  n3<=0 -> case{
      n2>0 -> ensures prio_queue1'= prio_queue1 & prio_queue3'=prio_queue3 &
      (exists x, r: prio_queue2::x*r::dll<p,n2-1> & x::node2<_,_,_,_> & prio_queue2'=r & cur_proc' = x);
      n2<=0 -> case{
         n1>0 -> ensures prio_queue2'= prio_queue2 & prio_queue3'=prio_queue3 &
         (exists x, r: prio_queue1::x*r::dll<p,n1-1> & x::node2<_,_,_,_> & prio_queue1'=r & cur_proc' = x);
         n1<=0 -> ensures prio_queue1'= prio_queue1 &  ensures  prio_queue2'= prio_queue2 &
                                 prio_queue3'=prio_queue3 & cur_proc' = null;
      }
    }
  }
}
{
    cur_proc = null;
    if (n3 > 0){
      cur_proc = prio_queue3;
      prio_queue3 = del_ele(prio_queue3, cur_proc);
      return;
    }
    if (n2 > 0){
      cur_proc = prio_queue2;
      prio_queue2 = del_ele(prio_queue2, cur_proc);
      return;
    }
    if (n1 > 0){
      cur_proc = prio_queue1;
      prio_queue1 = del_ele(prio_queue1, cur_proc);
      return;
    }
    //    for (i=/*MAXPRIO*/3; i > 0; i--)
    /*    {
	if (prio_queue[i]->mem_count > 0)
	{
	    cur_proc = prio_queue[i]->first;
	    prio_queue[i] = del_ele(prio_queue[i], cur_proc);
	    return;
	}
    }
    */
}

void upgrade_process_prio(int prio, int ratio)
  requires prio>0 & prio <=3
  ensures true;
{
    int count;
    int n;
    node2 proc;
    node2 src_queue, dest_queue;
    
    if (prio >= /*MAXPRIO*/3)
	return;
    if (prio == 1) {
      src_queue =  prio_queue1;
      dest_queue = prio_queue2;
    }
    if (prio == 2) {
      src_queue =  prio_queue2;
      dest_queue = prio_queue3;
    }
    // src_queue = prio_queue[prio];
    //dest_queue = prio_queue[prio+1];
    count = get_mem_count(src_queue);

    if (count > 0)
      {
        n = ratio;//(int) (count*ratio + 1);
        assume(n<count);
        proc = find_nth(src_queue, n);
        if (proc != null) {
          src_queue = del_ele(src_queue, proc);
          /* append to appropriate prio queue */
          proc.priority = prio;
          dest_queue = append_ele(dest_queue, proc);
        }
    }
}

void unblock_process(int ratio)
  requires block_queue::dll<_,n>*prio_queue1::dll<_,n1> * prio_queue2::dll<_,n2> * prio_queue3::dll<_,n3>
  ensures block_queue'::dll<_,n-1> & ((prio_queue1'::dll<_,n1+1> & prio_queue2'= prio_queue2 & prio_queue3'=prio_queue3) |
    (prio_queue2'::dll<_,n2+1> & prio_queue1'= prio_queue1 & prio_queue3'=prio_queue3)|
     (prio_queue3'::dll<_,n3+1> & prio_queue1'= prio_queue1 & prio_queue2'=prio_queue2));
{
    int count;
    int n;
    node2 proc;
    int prio;
    if (block_queue != null)
    {
      count = get_mem_count(block_queue);
      n = ratio;//(int) (count*ratio + 1);
      assume(n<count);
      proc = find_nth(block_queue, n);
      if (proc != null) {
	    block_queue = del_ele(block_queue, proc);
	    /* append to appropriate prio queue */
	    prio = proc.priority;
        if (prio == 1)
          prio_queue1 = append_ele(prio_queue1, proc);
        if (prio == 2)
          prio_queue2 = append_ele(prio_queue2, proc);
        if (prio == 3)
          prio_queue3 = append_ele(prio_queue3, proc);
      }
    }
}

void quantum_expire()
  requires prio_queue1::dll<_,n1> * prio_queue2::dll<_,n2> * prio_queue3::dll<_,n3>
  ensures ((prio_queue1'::dll<_,n1-1> & prio_queue2'= prio_queue2 & prio_queue3'=prio_queue3) |
    (prio_queue2'::dll<_,n2-1> & prio_queue1'= prio_queue1 & prio_queue3'=prio_queue3)|
     (prio_queue3'::dll<_,n3-1> & prio_queue1'= prio_queue1 & prio_queue2'=prio_queue2));//'
{
    int prio;
    schedule();
    if (cur_proc != null)
    {
      prio = cur_proc.priority;
       if (prio == 1)
          prio_queue1 = append_ele(prio_queue1, cur_proc);
        if (prio == 2)
          prio_queue2 = append_ele(prio_queue2, cur_proc);
        if (prio == 3)
          prio_queue3 = append_ele(prio_queue3, cur_proc);
    }
}

void block_process()
   requires block_queue::dll<_,n>
  ensures block_queue'::dll<_,n+1> //'
{
    schedule();
    if (cur_proc != null)
    {
      block_queue = append_ele(block_queue, cur_proc);
    }
}

node2 new_process(int prio)
  requires prio>0 & prio<=3
  ensures num_processes'= num_processes+1 & alloc_proc_num' = alloc_proc_num+1 &
          res::node<alloc_proc_num', prio, null, null>  //'
{
    node2 proc;
    proc = new_ele(alloc_proc_num++);
    proc.priority = prio;
    num_processes++;
    return proc;
}

void add_process(int prio)
  requires prio_queue1::dll<_,n1> * prio_queue2::dll<_,n2> * prio_queue3::dll<_,n3> & prio>0 & prio<=3
     case {
    prio = 1 -> ensures  prio_queue1'::dll<_,n1+1> & prio_queue2'= prio_queue2 & prio_queue3'=prio_queue3;
    prio = 2 -> ensures  prio_queue2'::dll<_,n2+1> & prio_queue1'= prio_queue1 & prio_queue3'=prio_queue3;
    prio = 3 -> ensures  prio_queue3'::dll<_,n3+1> & prio_queue1'= prio_queue1 & prio_queue2'=prio_queue2;//'
    prio <= 0 | prio >3 -> ensures true;
 }
{
    node2 proc;
    proc = new_process(prio);
    if (prio == 1)
      prio_queue1 = append_ele(prio_queue1, cur_proc);
    if (prio == 2)
      prio_queue2 = append_ele(prio_queue2, cur_proc);
    if (prio == 3)
      prio_queue3 = append_ele(prio_queue3, cur_proc);
    // prio_queue[prio] = append_ele(prio_queue[prio], proc);
}

node2 init_prio_queue_helper(node2 queue, int prio, int i, int n)
   requires prio>0 & prio<=3 & i<n
   ensures i >= n & res::dll<_, n>
{
  if (i>= n) return queue;
  proc = new_process(prio);
  queue = append_ele(queue, proc);
  return init_prio_queue_helper(queue, prio, i+1, n);
}

void init_prio_queue(int prio, int num_proc)
   requires prio>0 & prio<=3
   case {
    prio = 1 -> ensures  prio_queue1'::dll<_,num_proc> & prio_queue2'= prio_queue2 & prio_queue3'=prio_queue3;
    prio = 2 -> ensures  prio_queue2'::dll<_,num_proc> & prio_queue1'= prio_queue1 & prio_queue3'=prio_queue3;
    prio = 3 -> ensures  prio_queue3'::dll<_,num_proc> & prio_queue1'= prio_queue1 & prio_queue2'=prio_queue2;//'
    prio <= 0 | prio >3 -> ensures true;
{
    node2 queue = null;
    node2 proc;
    int i;

    //queue = new_list();
    /*for (i=0; i<num_proc; i++)
    {
	proc = new_process(prio);
	queue = append_ele(queue, proc);
    }*/
    queue = init_prio_queue_helper(queue, prio, 0, num_proc);
     if (prio == 1)
      prio_queue1 = queue;
    if (prio == 2)
      prio_queue2 = queue;
    if (prio == 3)
      prio_queue3 = queue;
    //   prio_queue[prio] = queue;
}

void initialize()
  requires true
  ensures alloc_proc_num' = 0 & num_processes' = 0;
{
    alloc_proc_num = 0;
    num_processes = 0;
}

/* test driver */
//main(argc, argv)
//int argc;
//char *argv[];
//{
//    int command;
//    int prio;
//    float ratio;
//    int status;

//    if (argc < (/*MAXPRIO*/3+1))
//    {
//	fprintf(stdout, "incorrect usage\n");
//	return;
//    }
    
//    initialize();
//    for (prio=/*MAXPRIO*/; prio >= 1; prio--)
//    {
//	init_prio_queue(prio, atoi(argv[prio]));
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
//}

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


