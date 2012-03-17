data node{
    int id;
    int priority;
    node next;
}

ll1<n> == self=null & n=0
  or self::node<_, v2, q> * q::ll1<n-1> & v2>=1 & v2<=3
	inv n>=0;

lseg1<p, n> == self=p & n=0
  or self::node<_,v2, q> * q::lseg1<p, n-1>& v2>=1 & v2<=3
	inv n>=0;

lemma self::ll1<n> <-> self::lseg1<null,n>;
//lemma self::lseg<p,n> * p::node<_,_, q>  -> self::lseg<q,n+1>;
lemma "V2" self::lseg1<p,n> & n = a + b & a,b >=0 <-> self::lseg1<r,a> * r::lseg1<p,b>;

int get_mem_count1(node x)
  requires x::ll1<n>
  ensures x::ll1<n> & res=n;

global node current_job;
global int next_pid;
global node prio_queue0;/* blocked queue is [0] */
global node prio_queue1;
global node prio_queue2;
global node prio_queue3;



int enqueue(int prio, node new_process,ref node curJob,ref node pq0, ref node pq1,
            ref node pq2, ref node pq3)
requires pq0::ll1<n>*pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>*new_process::node<v1,v2,null>  & v2>=1 & v2<=3
 case{
  prio = 0 -> case {
    curJob = null -> case{
      n1+n2+n3>0 -> 
      ensures pq0'::lseg1<new_process,n>*pq1'::ll1<n4>*pq2'::ll1<n5>*
      pq3'::ll1<n6>*new_process::node<_,v2,null>*curJob'::node<_,v3,null> & v2>=1 & v2<=3 & v3>=1 & v3<=3 & n4+n5+n6=n1+n2+n3-1 &res = 0;
      n1+n2+n3<=0 -> 
      ensures pq0'::lseg1<new_process,n>*pq1'::ll1<n1>*pq2'::ll1<n2>*
      pq3'::ll1<n3>* new_process::node<_,v2,null> & v2>=1 & v2<=3 & curJob'=null & res = 0;
    }
   curJob != null ->requires curJob::node<v3,v,null>& v>=1 & v<=3
     ensures pq0'::lseg1<new_process,n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*
    new_process::node<v1,v2,null>*curJob::node<v3,v,null> & v2>=1 & v2<=3 & v>=1 & v<=3 & curJob'=curJob & res = 0;
  }
  prio >= 1 & prio<=3 -> case {
    curJob = null -> requires v2=prio
      ensures pq0'::ll1<n>*pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
      curJob'::node<_,v4,null> & v4>=1 & v4<=3 & n4+n5+n6=n1+n2+n3 & res = 0;
    curJob != null -> requires curJob::node<_,v,null> & v2=prio & v>=1 & v<=3
    ensures pq0'::ll1<n>*pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
      curJob'::node<_,v4,null> & v4>=1 & v4<=3 & n4+n5+n6=n1+n2+n3+1 & res = 0;
  }
  prio > 3 | prio < 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*
    new_process::node<v1,v2,null>  & res = -4;
 }

relation EQ1(int a).
relation EQ2(int a).
relation EQ3(int a).
relation EQ4(int a).
relation EQ5(int a).
relation EQ6(int a).
relation EQ7(int a).
int enqueue1(int prio, node new_process,ref node curJob,ref node pq0, ref node pq1,
            ref node pq2, ref node pq3)
  infer [EQ1,EQ2,EQ3,EQ4,EQ5,EQ6,EQ7]
  requires pq0::ll1<n>*pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>*new_process::node<v1,v2,null>  & v2>=1 & v2<=3
 case{
  prio = 0 -> case {
    curJob = null -> case{
      n1+n2+n3>0 -> 
      ensures pq0'::lseg1<new_process,n>*pq1'::ll1<n4>*pq2'::ll1<n5>*
      pq3'::ll1<n6>*new_process::node<_,v2,null>*curJob'::node<_,v3,null> & EQ3(v2) & EQ4(v3);
      n1+n2+n3<=0 -> 
      ensures pq0'::lseg1<new_process,n>*pq1'::ll1<n1>*pq2'::ll1<n2>*
      pq3'::ll1<n3>* new_process::node<_,v2,null> & EQ2(v2);
    }
   curJob != null ->requires curJob::node<v3,v,null>& v>=1 & v<=3
     ensures pq0'::lseg1<new_process,n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*
    new_process::node<v1,v2,null>*curJob::node<v3,v,null> & EQ5(v2) & EQ6(v);
  }
  prio >= 1 & prio<=3 -> case {
    curJob = null -> requires v2=prio
      ensures pq0'::ll1<n>*pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
      curJob'::node<_,v4,null> &EQ7(v4);
    curJob != null -> requires curJob::node<_,v,null> & v2=prio & v>=1 & v<=3
    ensures pq0'::ll1<n>*pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
      curJob'::node<_,v4,null> & EQ1(v4);
  }
  prio > 3 | prio < 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*
    new_process::node<v1,v2,null> ;
 }
 
{
    int status;
    status = put_end(prio, new_process,pq0,pq1,pq2,pq3);
    if(status != 0) return (status); 
    status = reschedule(prio,curJob,pq1,pq2,pq3);
    return (status);
}

/* n3, n2, n1 : # of processes at prio3 ... */
void main(int argc, ref int  next_pid, ref node curJob, ref node pq0, 
	  ref node pq1, ref node pq2, ref node pq3)
requires  pq0::ll1<n>*pq1::ll1<n1> * pq2::ll1<n2> * pq3::ll1<n3> & next_pid=0 & curJob=null
ensures true;
{
    int command, prio;
    int ratio;
    int nprocs, status, pid;
    node process;

    prio = 3;
    status = new_job(prio, next_pid, curJob,pq1,pq2,pq3);
    if (status != 0) exit_here(status);
    get_command(command, prio, ratio);
    curJob=null;
    prio = 1;
    command = 1;
    schedule(command, prio, ratio,curJob, pq0,pq1,pq2,pq3);
    exit_here(0);
}

void sscanf(ref int cmd)
 requires true
  ensures (cmd'=1) or (cmd'=2) or (cmd'=3) or (cmd'=4)  or (cmd'=5)
 or (cmd'=6) or (cmd'=7);

void psscanf(ref int p)
 requires p=-1
  ensures p'=2;

 void psscanf2(ref int p1, ref int p2)
 requires p1=-1 & p2=-1
  ensures p1'=2 & p2'=2;

void get_command(ref int cmd, ref int prio, ref int ratio)
  requires true
  ensures (cmd'=1 & prio' = 2 & ratio'=-1) or (cmd'=4 & prio' = -1 & ratio'=2)
  or (cmd'=2 & prio' =2 & ratio'=2) or (cmd'=3 & prio' = -1 & ratio' =-1)
  or (cmd'=5 & prio'= -1 & ratio'=-1) or (cmd'=6 & prio' = -1 & ratio' =-1)
  or (cmd'=7 & prio' = -1 & ratio' =-1);
{
  prio = -1;
  cmd = -1;
  ratio = -1;
	sscanf(cmd);
	if(cmd==1) 
	    psscanf(prio);
	else if(cmd==4)
	    psscanf(ratio);
	else if(cmd==2)
	  psscanf2( prio, ratio);
}

void exit_here(int status)
  requires true
  ensures true;

/* allocate new pid and process block. Stick at end */
int new_job(int prio,ref int npid,ref node curJob,ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3> & prio>=1 & prio<=3
case {
  prio = 0 -> ensures true; 
  prio >= 1 & prio<=3 -> case{
    curJob = null -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
      curJob'::node<_,v2,null> & n4+n5+n6=n1+n2+n3 & npid'=npid +1 & res = 0 & v2>=1 & v2<=3;
    curJob != null ->requires curJob::node<_,v,null> & v>=1 & v<=3
      ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6> *curJob'::node<_,v3,null>
      & n4+n5+n6=n1+n2+n3+1 & npid'=npid +1 &res = 0 & v3>=1 & v3<=3;
  }
  prio > 3 | prio < 0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & npid'=npid &res = -4;
 }

relation NJ1(int a).
relation NJ2(int a).
int new_job1(int prio,ref int npid,ref node curJob,ref node pq1, ref node pq2, ref node pq3)
 infer [NJ1,NJ2]
 requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3> & prio>=1 & prio<=3
case {
  prio = 0 -> ensures true;
  prio >= 1 & prio<=3 -> case{
    curJob = null -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
      curJob'::node<_,v2,null> & n4+n5+n6=n1+n2+n3 & npid'=npid +1 & res = 0 & NJ1(v2);
    curJob != null ->requires curJob::node<_,v,null> & v>=1 & v<=3
      ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6> *curJob'::node<_,v3,null>
      & n4+n5+n6=n1+n2+n3+1 & npid'=npid +1 &res = 0 & NJ2(v3);
  }
  prio > 3 | prio < 0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & npid'=npid &res = -4;
 }
{
  int status = 0;
  node new_process, tmp;
  npid = npid + 1;
  new_process = new node(npid, prio, null);
  tmp = null;
  status = enqueue(prio, new_process, curJob,tmp,pq1,pq2,pq3);
  if(status != 0)
  {
    free(new_process); // Return process block
    npid = npid -1; // Unsuccess. Restore pid
  }
  return (status);
  }


/* increment priority at ratio in queue */
int upgrade_prio(int prio,int ratio,ref node curJob,ref node pq1,ref node pq2,ref node pq3)
  requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
  case{
    prio = 1 -> case {
      ratio < 1 | ratio > n1 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n1 ->  case {
	n1 = 0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res = 0;
	n1 != 0 -> case {
	  curJob = null -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
            curJob'::node<_,v2,null> & n4+n5+n6=n1+n2+n3-1 & res=0 & v2>=1 & v2<=3;
	  curJob != null -> requires curJob::node<_,v,null>& v>=1 & v<=3
	   ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
            curJob'::node<_,v2,null> & n4+n5+n6=n1+n2+n3 & res=0 & v2>=1 & v2<=3;
	}
      }
    }
    prio = 2 -> case {
      ratio < 1 | ratio > n2 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n2 ->  case {
	n2 = 0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res = 0;
	n2 != 0 ->case {
	  curJob = null -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
            curJob'::node<_,v2,null> & n4+n5+n6=n1+n2+n3-1 & res=0 & v2>=1 & v2<=3;
	  curJob != null -> requires curJob::node<_,v,null>& v>=1 & v<=3
	   ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
            curJob'::node<_,v2,null> & n4+n5+n6=n1+n2+n3 & res=0 & v2>=1 & v2<=3;
	}
      }
    }
    prio > 2 | prio <1 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-4;
  }


int upgrade_prio1(int prio,int ratio,ref node curJob,ref node pq1,ref node pq2,ref node pq3)
 requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
  case{
    prio = 1 -> case {
      ratio < 1 | ratio > n1 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n1 ->  case {
	n1 = 0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res = 0;
	n1 != 0 -> case {
	  curJob = null -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
            curJob'::node<_,v2,null> & n4+n5+n6=n1+n2+n3-1 & res=0 & v2>=1 & v2<=3;
	  curJob != null -> requires curJob::node<_,v,null>& v>=1 & v<=3
	   ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
            curJob'::node<_,v2,null> & n4+n5+n6=n1+n2+n3 & res=0 & v2>=1 & v2<=3;
	}
      }
    }
    prio = 2 -> case {
      ratio < 1 | ratio > n2 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n2 ->  case {
	n2 = 0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res = 0;
	n2 != 0 ->case {
	  curJob = null -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
            curJob'::node<_,v2,null> & n4+n5+n6=n1+n2+n3-1 & res=0 & v2>=1 & v2<=3;
	  curJob != null -> requires curJob::node<_,v,null>& v>=1 & v<=3
	   ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
            curJob'::node<_,v2,null> & n4+n5+n6=n1+n2+n3 & res=0 & v2>=1 & v2<=3;
	}
      }
    }
    prio > 2 | prio <1 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-4;
  }
{
  int status;
  node job, tmp;
  tmp = null;
  if(prio < 1 || prio > 2) 
    return (-4);
  status = get_process(prio, ratio, job, tmp,pq1,pq2,pq3);
  if(status <= 0) 
    return (status);
  /* We found a job in that queue. Upgrade it */
  job.priority = prio + 1;
  status = enqueue(prio + 1, job, curJob, tmp,pq1,pq2,pq3);
  return status;
}

/* Put current job in blocked queue */
int block(ref node curJob, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
 requires pq0::ll1<n>*pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
 case { curJob=null -> ensures true;
   curJob!=null -> requires curJob::node<_,v2,null> & v2>=1 & v2<=3 ensures true;
}

int block1(ref node curJob, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  requires pq0::ll1<n>*pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
  case { 
  curJob=null -> ensures true;
  curJob!=null -> 
    requires curJob::node<_,v2,null> & v2>=1 & v2<=3 
    ensures true;
  }
{
  node job;
  job = get_current(curJob, pq1, pq2, pq3);
  if(job != null)
  {
    curJob = null;
    return (enqueue(0, job,curJob, pq0,pq1,pq2,pq3));
  // BLOCKPRIO 0 put into blocked queue 
  }
  return 0;//OK 0
}

/* Restore job @ ratio in blocked queue to its queue */
int unblock(int ratio,ref node curJob, ref node pq0,ref node pq1, ref node pq2, ref node pq3)
  requires pq0::ll1<n>*pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
 case {
   ratio  < 1 | ratio > n -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
    ratio >= 1 & ratio <= n -> case{
      n=0 -> ensures  pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=0;
      n!=0 -> case {
	curJob = null -> ensures pq0'::ll1<n-1>*pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
	  curJob'::node<_,v4,null> & res=0 & n4+n5+n6=n1+n2+n3 & v4>=1 & v4<=3;
        curJob != null -> requires curJob::node<_,v,null> & v>=1 & v<=3
	   ensures pq0'::ll1<n-1>*pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
	  curJob'::node<_,v4,null> & res=0 & n4+n5+n6=n1+n2+n3+1 & v4>=1 & v4<=3;
      }

    }
}

relation UB1(int a).
relation UB2(int a).
int unblock1(int ratio,ref node curJob, ref node pq0,ref node pq1, ref node pq2, ref node pq3)
 infer [UB1,UB2]
  requires pq0::ll1<n>*pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
 case {
   ratio  < 1 | ratio > n -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
    ratio >= 1 & ratio <= n -> case{
      n=0 -> ensures  pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=0;
      n!=0 -> case {
	curJob = null -> ensures pq0'::ll1<n-1>*pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
	  curJob'::node<_,v4,null> & res=0 & n4+n5+n6=n1+n2+n3 & UB1(v4);
        curJob != null -> requires curJob::node<_,v,null> & v>=1 & v<=3
	   ensures pq0'::ll1<n-1>*pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
	  curJob'::node<_,v4,null> & res=0 & n4+n5+n6=n1+n2+n3+1 & UB2(v4);
      }

    }
}
{
  int status;
  node job;
  status = get_process(0, ratio, job,pq0,pq1,pq2,pq3);
  if(status <= 0) return(status);//BLOCKPRIO 0
  /* We found a blocked process. Put it where it belongs. */
  status = enqueue(job.priority, job, curJob, pq0,pq1,pq2,pq3);
  return status;
}

/* put current job at end of its queue */
int quantum_expire(ref node curJob,ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
 case {
  curJob = null -> case {
    n1+n2+n3>0 -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*curJob'::node<_,v4,null>
    & res=0 & n4+n5+n6=n1+n2+n3-1 & v4>=1 & v4<=3;
    n1+n2+n3<=0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=0 & curJob'=null;
  }
  curJob != null -> requires curJob::node<v1,v2,null> & v2>=1 & v2<=3
    ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*curJob'::node<_,v4,null>
    & res=0 & n4+n5+n6=n1+n2+n3 & v4>=1 & v4<=3;
  }

relation QE1(int a).
  relation QE2(int a).

int quantum_expire1(ref node curJob,ref node pq1, ref node pq2, ref node pq3)
 infer [QE1,QE2]
 requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
 case {
  curJob = null -> case {
    n1+n2+n3>0 -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*curJob'::node<_,v4,null>
    & res=0 & n4+n5+n6=n1+n2+n3-1 & QE1(v4);
    n1+n2+n3<=0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=0 & curJob'=null;
  }
  curJob != null -> requires curJob::node<v1,v2,null> & v2>=1 & v2<=3
    ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*curJob'::node<_,v4,null>
    & res=0 & n4+n5+n6=n1+n2+n3 & QE2(v4);
  }
{
  node  job, tmp;
    int status;
    job = get_current(curJob, pq1, pq2, pq3);
    if(job != null)
    {
      curJob = null;
      tmp = null;
      status = enqueue(job.priority, job, curJob, tmp, pq1, pq2, pq3);
      return status;
    }
    return 0; //OK 0
}

void free(ref node job)
  requires job::node<_,_,null>
  ensures job'=null;

int finish(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
   case {
  curJob =null -> case {
    n1=0 & n2=0 & n3=0 ->  ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> &
    curJob' = null  & res=1;
    n1!=0 | n2!=0 | n3!=0 -> ensures res=0;
  }
  curJob !=null -> requires curJob::node<_,_,null> case {
    n1+n2+n3>=1 -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
      curJob'::node<_,v2,null> & res=0 & n4+n5+n6=n1+n2+n3-1 & v2>=1 & v2<=3;
    (n1+n2+n3)<1 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>
      & curJob'=null & res=0;
  }
}

relation FI1(int a).
int finish1(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
  infer [FI1] 
  requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
   case {
  curJob =null -> case {
    n1=0 & n2=0 & n3=0 ->  ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> &
    curJob' = null  & res=1;
    n1!=0 | n2!=0 | n3!=0 -> ensures res=0;
  }
  curJob !=null -> requires curJob::node<_,_,null> case {
    n1+n2+n3>=1 -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*
      curJob'::node<_,v2,null> & res=0 & n4+n5+n6=n1+n2+n3-1 & FI1(v2);
    (n1+n2+n3)<1 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>
      & curJob'=null & res=0;
  }
}
{
    node job;
    job = get_current(curJob, pq1, pq2, pq3);
    if(job != null)
    {
	  curJob = null;
	  reschedule(0, curJob,pq1,pq2,pq3);
      free(job);
	  return 0; //FALSE 0
    }
    else return 1;//TRUE 1
}

/* Get all jobs in priority queues & zap them */
int flush(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
 case {
  curJob = null & n1=0 & n2=0 & n3=0 -> ensures pq1'=null & pq2'=null & pq3'=null &
  curJob' = null & res=0;
  curJob != null | n1!=0 | n2!=0 | n3!=0 -> requires curJob::node<_,_,null>
  ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6> &
      n4+n5+n6<=n1+n2+n3 & res=0;
}

int flush1(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
 requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
 case {
  curJob = null & n1=0 & n2=0 & n3=0 -> ensures pq1'=null & pq2'=null & pq3'=null &
  curJob' = null & res=0;
  curJob != null | n1!=0 | n2!=0 | n3!=0 -> requires curJob::node<_,_,null>
  ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6> &
      n4+n5+n6<=n1+n2+n3 & res=0;
}
{
  if (finish(curJob,pq1,pq2,pq3) == 0)
    {
    flush(curJob,pq1,pq2,pq3);
    }
    return 0;//OK 0
}


/* If no current process, get it. Return it */
node get_current(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
   requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
  case {
  curJob =null -> case {
    n3>0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3-1>*curJob'::node<_,v2,null> & res=curJob' & v2>=1 & v2<=3;
    n3<=0 -> case {
      n2>0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2-1>*pq3'::ll1<n3>*curJob'::node<_,v2,null> & res=curJob' & v2>=1 & v2<=3;
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll1<n1-1>*pq2'::ll1<n2>*pq3'::ll1<n3>*curJob'::node<_,v2,null> & res=curJob' & v2>=1 & v2<=3;
        n1<=0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & curJob'=null & res=null;
      }
    }
  }
  curJob !=null -> requires curJob::node<v1,v2,null>
    ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*curJob::node<v1,v2,null> &  curJob'=curJob& res=curJob;
}

relation GC1(int b).
relation GC2(int b).
relation GC3(int b).
node get_current1(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
  infer [GC1,GC2,GC3]
  requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
 case {
  curJob =null -> case {
    n3>0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3-1>*curJob'::node<_,v2,null> & GC1(v2) & res=curJob' ;
    n3<=0 -> case {
      n2>0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2-1>*pq3'::ll1<n3>*curJob'::node<_,v2,null> & GC2(v2) & res=curJob';
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll1<n1-1>*pq2'::ll1<n2>*pq3'::ll1<n3>*curJob'::node<_,v2,null> & GC3(v2)& res=curJob';
        n1<=0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & curJob'=null & res=null;
      }
    }
  }
  curJob !=null -> requires curJob::node<v1,v2,null>
  ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*curJob::node<v1,v2,null> & curJob'=curJob& res=curJob;
}
{
    int prio;
    if(curJob == null)
      {
      node tmp = null;
      if(do_get_process(1, curJob, pq3) > 0) return curJob;
      if(do_get_process(1, curJob, pq2) > 0) return curJob;
      if(do_get_process(1, curJob, pq1) > 0) return curJob;
    }
    return curJob;
}

 /* Put highest priority job into current_job */
int reschedule(int prio, ref node cur_job, ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
   case{
  cur_job = null -> case {
    n3>0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3-1>*cur_job'::node<_,v4,null> & v4>=1 & v4<=3 & res=0;
    n3<=0 -> case {
      n2>0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2-1>*pq3'::ll1<n3>*cur_job'::node<_,v4,null>  & v4>=1 & v4<=3 & res=0;
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll1<n1-1>*pq2'::ll1<n2>*pq3'::ll1<n3>*cur_job'::node<_,v4,null> & v4>=1 & v4<=3 & res=0;
        n1<=0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & cur_job'=null & res=0;
      }
    }
  }
  cur_job != null -> requires cur_job::node<v1,v2,null> & v2>=1 & v2 <=3 case {
    prio > v2 -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*cur_job'::node<_,v4,null> & n4+n5+n6=n1+n2+n3 & res=0 & v4>=1 & v4<=3;
   prio <= v2 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*cur_job::node<v1,v2,null> & cur_job'=cur_job & res=0;
  }
}

relation RESC1(int a).
relation RESC2(int a).
relation RESC3(int a).
  relation RESC4(int a).
int reschedule1(int prio, ref node cur_job, ref node pq1, ref node pq2, ref node pq3)
  infer [RESC1,RESC2,RESC3,RESC4]
  requires pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
 case{
  cur_job = null -> case {
    n3>0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3-1>*cur_job'::node<_,v4,null> & RESC1(v4) & res=0;
    n3<=0 -> case {
      n2>0 ->ensures pq1'::ll1<n1>*pq2'::ll1<n2-1>*pq3'::ll1<n3>*cur_job'::node<_,v4,null> & RESC2(v4) & res=0;
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll1<n1-1>*pq2'::ll1<n2>*pq3'::ll1<n3>*cur_job'::node<_,v4,null> & RESC3(res) & res=0;
        n1<=0 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & cur_job'=null & res=0;
      }
    }
  }
  cur_job != null -> requires cur_job::node<v1,v2,null> & v2>=1 & v2 <=3 case {
    prio > v2 -> ensures pq1'::ll1<n4>*pq2'::ll1<n5>*pq3'::ll1<n6>*cur_job'::node<_,v4,null> & RESC4(v4) & n4+n5+n6=n1+n2+n3 & res=0 ;
    prio <= v2 -> ensures pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*cur_job::node<v1,v2,null>  & cur_job'=cur_job & res=0;
  }
}
{
    if(cur_job != null)
    {
      if (prio > cur_job.priority){
        node tmp = null;
        put_end(cur_job.priority, cur_job, tmp,pq1,pq2,pq3);
        cur_job = null;//(struct process *)0;
      }
    }
    cur_job = get_current(cur_job, pq1, pq2, pq3); // Reschedule
    return 0;//OK 0
}

int schedule(int command, int prio, int ratio,ref node curJob,ref node pq0, ref node pq1, ref node pq2, ref node pq3)
    requires pq0::ll1<n>*pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3> & command >= 1 & command <= 7 & prio>=1 & prio<=3
 case {
  command = 1 ->  case {
    curJob=null -> ensures true;
    curJob!=null ->  requires curJob::node<_,v,null> & v>=1 & v<=3 ensures true;
  }
  command = 2 -> case {
    curJob=null -> ensures true;
    curJob!=null ->  requires curJob::node<_,v,null> & v>=1 & v<=3 ensures true;
  }
  command = 3 -> case { curJob=null -> ensures true;
  curJob!=null -> requires curJob::node<_,v2,null> & v2>=1 & v2<=3 ensures true;
  }
  command = 4 -> case {
    curJob=null -> ensures true;
    curJob!=null ->  requires curJob::node<_,v,null> & v>=1 & v<=3 ensures true;
  }
  command = 5 -> case {
    curJob=null -> ensures true;
    curJob!=null ->  requires curJob::node<_,v,null> & v>=1 & v<=3 ensures true;
  }
  command = 6 -> case {
    curJob =null -> case {
      n1=0 & n2=0 & n3=0 ->  ensures true;
      n1!=0 | n2!=0 | n3!=0 -> ensures true;
    }
    curJob !=null -> requires curJob::node<_,_,null> case {
      n1+n2+n3>=1 -> ensures true;
      (n1+n2+n3)<1 -> ensures true;
    }
  }
  command = 7 -> case {
    curJob = null & n1=0 & n2=0 & n3=0 -> ensures true;
    curJob != null | n1!=0 | n2!=0 | n3!=0 -> requires curJob::node<_,_,null>  ensures true;
  }
  command < 1 | command > 7 -> ensures res = -6;
  }
{
    int status = 0;//OK 0
    if(command == 1) //NEW_JOB 1
    {
      status = new_job(prio, next_pid,curJob,pq1,pq2,pq3);
	}
	else if (command == 5) //QUANTUM_EXPIRE 5
	{
      status = quantum_expire(curJob, pq0,pq1,pq2,pq3);
	}
	else if (command == 2) //UPGRADE_PRIO 2
	{
      status = upgrade_prio(prio, ratio,curJob, pq1,pq2,pq3);
	}
	else if(command== 3) // BLOCK 3
	{
        status = block(curJob,pq0,pq1,pq2,pq3);
	}
	else if (command == 4)// UNBLOCK 4
	{
      status = unblock(ratio,curJob,pq0,pq1,pq2,pq3);
	}
	else if (command == 6)//FINISH :6
    {    finish(curJob,pq1,pq2,pq3);
	}
	else if (command ==7)// FLUSH :7
	{
        status = flush(curJob,pq1,pq2,pq3);
    }
	else status = -6;//NO_COMMAND -6;

    return status;
}

node lput_end(node x, node y)
   requires y::node<v1,v2,null>
 case {
  x = null -> ensures y::node<v1,v2,null> & res = y;
  x != null -> requires x::ll1<n> ensures res::lseg1<y,n>*y::node<v1,v2,null>;
    }
{
  if (x==null)
    {
      return y;
    }
  node tmp=x.next;
  x.next=lput_end(tmp,y);
  return x;
}


 /* Put process at end of queue */
int put_end(int prio, node process, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  requires pq0::ll1<n>*pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>*process::node<v1,v2,null>
   &v2>=1 & v2<=3
 case{
   prio = 0 -> ensures pq0'::lseg1<process,n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*process::node<v1,v2,null> & res = 0;
   prio = 1 -> requires v2=prio ensures pq0'::ll1<n>*pq1'::lseg1<process,n1>*pq2'::ll1<n2>*pq3'::ll1<n3>* process::node<v1,v2,null> & res = 0;
   prio = 2 -> requires v2=prio ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::lseg1<process,n2>*pq3'::ll1<n3>*process::node<v1,v2,null> & res = 0;
   prio = 3 -> requires v2=prio ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::lseg1<process,n3>*process::node<v1,v2,null> & res = 0;
   prio > 3 | prio < 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*
   process::node<v1,v2,null> & res = -4;
 }

int put_end1(int prio, node process, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
requires pq0::ll1<n>*pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>*process::node<v1,v2,null>
   &v2>=1 & v2<=3
 case{
   prio = 0 -> ensures pq0'::lseg1<process,n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*process::node<v1,v2,null> & res = 0;
   prio = 1 -> requires v2=prio ensures pq0'::ll1<n>*pq1'::lseg1<process,n1>*pq2'::ll1<n2>*pq3'::ll1<n3>* process::node<v1,v2,null> & res = 0;
   prio = 2 -> requires v2=prio ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::lseg1<process,n2>*pq3'::ll1<n3>*process::node<v1,v2,null> & res = 0;
   prio = 3 -> requires v2=prio ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::lseg1<process,n3>*process::node<v1,v2,null> & res = 0;
   prio > 3 | prio < 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3>*
   process::node<v1,v2,null> & res = -4;
 }
{
    node next;
    if(prio > 3 || prio < 0) return (-4); /* Somebody goofed MAXPRIO 3 BADPRIO -4*/
     /* find end of queue */
    if (prio == 0)
      pq0 = lput_end(pq0, process);
    else if (prio == 1)
      pq1 = lput_end(pq1, process);
    else if (prio == 2)
      pq2 = lput_end(pq2, process);
    else if (prio == 3)
      pq3 = lput_end(pq3, process);
    return (0);//OK 0
}

node del_ele(ref node x, node ele)
  requires (exists j,q: x::lseg1<ele,j> * ele::node<v1,v2,q> * q::ll1<m>) //&  v2 >=0 & v2 <= 3
  ensures x'::lseg1<q,j> * q::ll1<m> * ele::node<v1,v2,q>& v2 >=0 & v2 <= 3 & res=x';

node find_nth(node f_list, int j)
  requires j>=1
 case {
  f_list!=null -> requires f_list::ll1<n> & j<=n
    ensures (exists q: f_list::lseg1<res,j-1> * res::node<_,v2,q> * q::ll1<n-j> & v2>=1 & v2<=3);
  f_list = null -> ensures f_list=null & res=null;
}

int do_get_process(int ratio, ref node job, ref node pq0)
  requires pq0::ll1<n>
 case {
  ratio < 1 | ratio > n -> ensures pq0'::ll1<n> & res=-5 & job'=job;
  ratio >= 1 & ratio <= n -> case{
    n = 0 -> ensures pq0'=null & job'=null & res = 0;
    n != 0 -> ensures pq0'::ll1<n-1> * job'::node<_,v4,null> & res = 1 & v4>=1 & v4<=3;
  }
}
{
  int length;
  int index;
  length = get_mem_count1(pq0);
  if(ratio < 1 || ratio > length) return (-5); /* Somebody else goofed BADRATIO -5*/
  index = ratio ;//* length;

  job = find_nth(pq0, index);//index

  if(job != null)
    {
      pq0 = del_ele(pq0, job);
      job.next = null;
      return 1;//TRUE 1
    }
  else return 0;//FALSE 0
}

int get_process(int prio, int ratio, ref node job, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  requires pq0::ll1<n>*pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
 case {
    prio = 0 -> case {
      ratio < 1 | ratio > n -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n -> case{
      n = 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & job'=null & res = 0;
      n != 0 -> ensures pq0'::ll1<n-1>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> * job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1;
      }
    }
    prio = 1 -> case {
      ratio < 1 | ratio > n1 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n1 -> case{
      n1 = 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & job'=null & res = 0;
      n1 != 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1-1>*pq2'::ll1<n2>*pq3'::ll1<n3> * job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1;
      }
    }
    prio = 2 -> case {
      ratio < 1 | ratio > n2 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n2 -> case{
      n2 = 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & job'=null & res = 0;
      n2 != 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2-1>*pq3'::ll1<n3> * job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1;
      }
    }
    prio = 3 -> case {
      ratio < 1 | ratio > n3 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n3 -> case{
      n3 = 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & job'=null & res = 0;
      n3 != 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3-1> * job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1;
      }
    }
    prio > 3 | prio <0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-4;
}

relation GP1(int a).
relation GP2(int b).
relation GP3(int b).
relation GP4(int a).
int get_process1(int prio, int ratio, ref node job, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  infer [GP1, GP2, GP3,GP4]
requires pq0::ll1<n>*pq1::ll1<n1>*pq2::ll1<n2>*pq3::ll1<n3>
 case {
    prio = 0 -> case {
      ratio < 1 | ratio > n -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n -> case{
      n = 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & job'=null & res = 0;
      n != 0 -> ensures pq0'::ll1<n-1>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> * job'::node<_,v4,null> &  GP1(v4) & res = 1; 
      }
    }
    prio = 1 -> case {
      ratio < 1 | ratio > n1 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n1 -> case{
      n1 = 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & job'=null & res = 0;
      n1 != 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1-1>*pq2'::ll1<n2>*pq3'::ll1<n3> * job'::node<_,v4,null> & GP2(v4) & res = 1;
      }
    }
    prio = 2 -> case {
      ratio < 1 | ratio > n2 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n2 -> case{
      n2 = 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & job'=null & res = 0;
      n2 != 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2-1>*pq3'::ll1<n3> * job'::node<_,v4,null> & GP3(v4) & res = 1;
      }
    }
    prio = 3 -> case {
      ratio < 1 | ratio > n3 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-5;
      ratio >= 1 & ratio <= n3 -> case{
      n3 = 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & job'=null & res = 0;
      n3 != 0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3-1> * job'::node<_,v4,null> & GP4(v4) & res = 1;
      }
    }
    prio > 3 | prio <0 -> ensures pq0'::ll1<n>*pq1'::ll1<n1>*pq2'::ll1<n2>*pq3'::ll1<n3> & res=-4;
}
{
  int status;
  if(prio > 3 || prio < 0) return (-4); /* Somebody goofed MAXPRIO 3, BADPRIO -4*/
    else {
      if (prio == 0) status = do_get_process(ratio, job, pq0);
      else if (prio == 1) status = do_get_process(ratio, job, pq1);
      else if (prio == 2) status = do_get_process(ratio, job, pq2);
      else if (prio == 3) status = do_get_process(ratio, job, pq3);

      return status;
    }
}
