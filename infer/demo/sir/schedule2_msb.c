data node{
  int id;
  int priority;
  node next;
}

ll1<n,S> == self=null & n=0 & S={}
  or self::node<v, _, q> * q::ll1<n-1,S1> & S1=union(S,{v})
	inv n>=0;

lseg1<p, n,S> == self=p & n=0 & S={}
  or self::node<v,_, q> * q::lseg1<p, n-1,S1> & S1=union(S,{v})
	inv n>=0;

lemma self::ll1<n,S> <-> self::lseg1<null,n,S>;
lemma self::lseg1<p,n,S1> * p::node<v,_, q>  -> self::lseg1<q,n+1,S2> & S2=union(S1,{v});
lemma "V2" self::lseg1<p,n,S> & n = a + b & S = union(S1,S2) & a,b >=0 <-> self::lseg1<r,a,S1> * r::lseg1<p,b,S2>;

int get_mem_count1(node x)
     requires x::ll1<n,S>
     ensures x::ll1<n,S> & res=n;

global node current_job;
global int next_pid;
global node prio_queue0;/* blocked queue is [0] */
global node prio_queue1;
global node prio_queue2;
global node prio_queue3;

relation ENQ1(bag a, bag b).
int enqueue1(int prio, node new_process,ref node curJob,ref node pq0, ref node pq1,
            ref node pq2, ref node pq3)
  requires pq0::ll1<n,S0>*pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>*
  new_process::node<v1,v2,null> & v2>=1 & v2<=3
 case{
  prio = 0 -> case {
    curJob = null -> case{
      n1+n2+n3>0 ->
      ensures pq0'::lseg1<new_process,n,S0>*pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*
      pq3'::ll1<n6,S6>*new_process::node<_,v2,null>*curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3-1 & v4>=1 & v4<=3 &res = 0;
      n1+n2+n3<=0 ->
      ensures pq0'::lseg1<new_process,n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*
      pq3'::ll1<n3,S3>* new_process::node<_,v2,null> & v4>=1 & v4<=3 & curJob'=null & res = 0;
    }
   curJob != null ->requires curJob::node<v3,v,null>& v>=1 & v<=3
    ensures pq0'::lseg1<new_process,n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*
pq3'::ll1<n3,S3>*
    new_process::node<v1,v2,null>*curJob::node<v3,v,null> & curJob'=curJob & res = 0;
  }
 prio >= 1 & prio<=3 -> case {
    curJob = null -> requires v2=prio
      ensures pq0'::ll1<n,S0>*pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*
      curJob'::node<_,v4,null> & n4+n5+n6=n1+n2+n3 & v4>=1 & v4<=3 & res = 0;
    curJob != null -> requires curJob::node<_,v,null> & v2=prio & v>=1 & v<=3
      ensures pq0'::ll1<n,S0>*pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*
    curJob'::node<_,v4,null> & n4+n5+n6=n1+n2+n3+1 &v4>=1 & v4<=3 & res = 0;
  }
 prio > 3 | prio < 0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3>*
    new_process::node<v1,v2,null> & res = -4;
 }
{
    int status;
    status = put_end1(prio, new_process,pq0,pq1,pq2,pq3);
    if(status != 0) return (status); 
    status = reschedule1(prio,curJob,pq1,pq2,pq3);
    return (status);
}

/* n3, n2, n1 : # of processes at prio3 ... */
void main(int argc, ref int  next_pid, ref node curJob, ref node pq0, 
	  ref node pq1, ref node pq2, ref node pq3)
  requires  pq0::ll1<n,S0>*pq1::ll1<n1,S1> * pq2::ll1<n2,S2> * pq3::ll1<n3,S3> & next_pid=0 & curJob=null
ensures true;
{
    int command, prio;
    int ratio;
    int nprocs, status, pid;
    node process;

    prio = 3;
    status = new_job1(prio, next_pid, curJob,pq1,pq2,pq3);
    if (status != 0) exit_here(status);
    get_command(command, prio, ratio);
    curJob=null;
    prio = 1;
    command = 1;
    schedule(command, prio, ratio,curJob, pq0,pq1,pq2,pq3);
    exit_here(0);//OK 0
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
	if(cmd==1) //NEW_JOB
	    psscanf(prio);
	else if(cmd==4)//	  case UNBLOCK :
	    psscanf(ratio);
	else if(cmd==2)//	  case UPGRADE_PRIO :
	  psscanf2( prio, ratio);
}

void exit_here(int status)
  requires true
  ensures true;

/* allocate new pid and process block. Stick at end */
int new_job1(int prio,ref int npid,ref node curJob,ref node pq1, ref node pq2, ref node pq3)
      requires pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3> & prio>=1 & prio<=3
 case {
  prio = 0 -> ensures true; 
  prio >= 1 & prio<=3 -> case{
    curJob = null -> ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*
      curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3 & npid'=npid +1 & res = 0;
   curJob != null ->requires curJob::node<_,v,null> & v>=1 & v<=3
      ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6> *curJob'::node<_,v3,null>
      & n4+n5+n6=n1+n2+n3+1 & npid'=npid +1 &res = 0;
  }
  prio > 3 | prio < 0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & npid'=npid &res = -4;
 }

int new_job(int prio,ref int npid,ref node curJob,ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3> & prio>=1 & prio<=3
 case {
  prio = 0 -> ensures true; 
  prio >= 1 & prio<=3 -> case{
    curJob = null -> ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*
      curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3 & npid'=npid +1 & res = 0;
   curJob != null ->requires curJob::node<_,v,null> & v>=1 & v<=3
      ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6> *curJob'::node<_,v3,null>
      & n4+n5+n6=n1+n2+n3+1 & npid'=npid +1 &res = 0;
  }
  prio > 3 | prio < 0 -> ensures pq1'::ll1<n1,S11>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & npid'=npid &res = -4;
 }
{
  int status = 0;//OK 0
  node new_process, tmp;
  npid = npid + 1;
    new_process = new node(npid, prio, null);
    tmp = null;
    status = enqueue1(prio, new_process, curJob,tmp,pq1,pq2,pq3);
    if(status != 0)
      {
        free(new_process); // Return process block
        npid = npid -1; // Unsuccess. Restore pid
      }
    //if(status) next_pid--; // Unsuccess. Restore pid 
    return (status);
}

 /* increment priority at ratio in queue */
int upgrade_prio1(int prio,int ratio,ref node curJob,ref node pq1,ref node pq2,ref node pq3)
  requires pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
  case{
  prio = 1 -> case {
    ratio < 1 | ratio > n1 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-5;
    ratio >= 1 & ratio <= n1 ->  case {
      n1 = 0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res = 0;
      n1 != 0 -> case {
        curJob = null -> ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*
            curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3-1 & res=0;
	  curJob != null -> requires curJob::node<_,v,null>& v>=1 & v<=3
        ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*
            curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3 & res=0;
	}
      }
    }
  prio = 2 -> case {
    ratio < 1 | ratio > n2 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-5;
    ratio >= 1 & ratio <= n2 ->  case {
      n2 = 0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res = 0;
      n2 != 0 ->case {
        curJob = null -> ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*
            curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3-1 & res=0;
        curJob != null -> requires curJob::node<_,v,null>& v>=1 & v<=3
        ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*
            curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3 & res=0;
	}
      }
    }
  prio > 2 | prio <1 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-4;
  }
{
    int status;
    node job, tmp;
    tmp = null;
    if(prio < 1 || prio > 2) return (-4);//MAXLOPRIO 2; BADPRIO -4
    status = get_process1(prio, ratio, job, tmp,pq1,pq2,pq3);
    if(status <= 0) return (status);
    /* We found a job in that queue. Upgrade it */
    job.priority = prio + 1;
    status = enqueue1(prio + 1, job, curJob, tmp,pq1,pq2,pq3);
    return status;
}


/* Put current job in blocked queue */
int block1(ref node curJob, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  requires pq0::ll1<n,S0>*pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
 case { curJob=null -> ensures true;
  curJob!=null -> requires curJob::node<_,v2,null> & v2>=1 & v2<=3 ensures true;
}
{
    node job;
    job = get_current(curJob, pq1, pq2, pq3);
    if(job != null)
    {
      curJob = null;//(struct process *)0; // remove it
      return (enqueue1(0, job,curJob, pq0,pq1,pq2,pq3));
// BLOCKPRIO 0 put into blocked queue
    }
    return 0;//OK 0
}

/* Restore job @ ratio in blocked queue to its queue */
int unblock1(int ratio,ref node curJob, ref node pq0,ref node pq1, ref node pq2, ref node pq3)
  requires pq0::ll1<n,S0>*pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
 case {
  ratio  < 1 | ratio > n -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-5;
    ratio >= 1 & ratio <= n -> case{
      n=0 -> ensures  pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=0;
      n!=0 -> case {
        curJob = null -> ensures pq0'::ll1<n-1,S01>*pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*
	  curJob'::node<_,v4,null> & res=0 & n4+n5+n6=n1+n2+n3 & v4>=1 & v4<=3;
        curJob != null -> requires curJob::node<_,v,null> & v>=1 & v<=3
          ensures pq0'::ll1<n-1,S01>*pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*
	  curJob'::node<_,v4,null> & res=0 & n4+n5+n6=n1+n2+n3+1 & v4>=1 & v4<=3;
      }

    }
}
{
    int status;
    node job;
    status = get_process1(0, ratio, job,pq0,pq1,pq2,pq3);
    if(status <= 0) return(status);//BLOCKPRIO 0
    /* We found a blocked process. Put it where it belongs. */
    status = enqueue1(job.priority, job, curJob, pq0,pq1,pq2,pq3);
    return status;
}

/* put current job at end of its queue */
int quantum_expire1(ref node curJob,ref node pq1, ref node pq2, ref node pq3)
      requires pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
 case {
  curJob = null -> case {
    n1+n2+n3>0 -> ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*curJob'::node<_,v4,null>
    & res=0 & n4+n5+n6=n1+n2+n3-1 & v4>=1 & v4<=3;
    n1+n2+n3<=0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=0 & curJob'=null;
  }
  curJob != null -> requires curJob::node<v1,v2,null> & v2>=1 & v2<=3
    ensures  pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*curJob'::node<_,v4,null>
    & res=0 & n4+n5+n6=n1+n2+n3 & v4>=1 & v4<=3;
  }
{
  node  job, tmp;
    int status;
    job = get_current(curJob, pq1, pq2, pq3);
    if(job != null)
    {
      curJob = null;//(struct process *)0; /* remove it */
      tmp = null;
      status = enqueue1(job.priority, job, curJob, tmp, pq1, pq2, pq3);
      return status;
    }
    return 0; //OK 0
}

void free(ref node job)
  requires job::node<_,_,null>
  ensures job'=null;

int finish1(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
      requires pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
   case {
  curJob =null -> case {
    n1=0 & n2=0 & n3=0 ->  ensures  pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> &
    curJob' = null  & res=1;
    n1!=0 | n2!=0 | n3!=0 -> ensures res=0;
  }
  curJob !=null -> requires curJob::node<_,_,null> case {
    n1+n2+n3>=1 -> ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*
      curJob'::node<v,_,null> & res=0 & n4+n5+n6=n1+n2+n3-1 ;
    (n1+n2+n3)<1 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3>
      & curJob'=null & res=0;
  }
}
{
    node job;
    job = get_current(curJob, pq1, pq2, pq3);
    if(job != null)
    {
	  curJob = null;//(struct process *)0;
	  reschedule1(0, curJob,pq1,pq2,pq3);
      free(job);
	  return 0; //FALSE 0
    }
    else return 1;//TRUE 1
}

/* Get all jobs in priority queues & zap them */
int flush1(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
      requires pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
 case {
  curJob = null & n1=0 & n2=0 & n3=0 -> ensures pq1'=null & pq2'=null & pq3'=null &
  curJob' = null & res=0;
  curJob != null | n1!=0 | n2!=0 | n3!=0 -> requires curJob::node<_,_,null>
    ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6> &
      n4+n5+n6<=n1+n2+n3 & res=0;
}
{
  if (finish1(curJob,pq1,pq2,pq3) == 0)
    {
      flush1(curJob,pq1,pq2,pq3);
    }
    return 0;//OK 0
}


/* If no current process, get it. Return it */
node get_current(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
requires pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
 case {
  curJob =null -> case {
    n3>0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3-1,S31>*curJob'::node<v,v2,null> & res=curJob' & v2>=1 & v2<=3 & S3=union(S31,{v});
    n3<=0 -> case {
      n2>0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2-1,S21>*pq3'::ll1<n3,S3>*curJob'::node<v,v2,null> & res=curJob' & v2>=1 & v2<=3& S2=union(S21,{v});
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll1<n1-1,S11>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3>*curJob'::node<v,v2,null> & res=curJob' & v2>=1 & v2<=3 & S1=union(S11,{v});
      n1<=0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & curJob'=null & res=null;
      }
    }
  }
  curJob !=null -> requires curJob::node<v1,v2,null>
  ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3>*curJob::node<v1,v2,null> &  curJob'=curJob& res=curJob;
}

relation GC1(bag a, bag b, int c).
relation GC2(bag a, bag b, int c).
relation GC3(bag a, bag b, int c).
relation GC11(bag a, bag b).
relation GC12(bag a, bag b).
relation GC21(bag a, bag b).
relation GC22(bag a, bag b).
relation GC31(bag a, bag b).
relation GC32(bag a, bag b).
relation GC41(bag a, bag b).
relation GC42(bag a, bag b).
relation GC43(bag a, bag b).
relation GC51(bag a, bag b).
relation GC52(bag a, bag b).
relation GC53(bag a, bag b).
node get_current1(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
  infer [GC1,GC2,GC3,GC11,GC12,GC21,GC22,GC31,GC32,GC41,GC42,GC43,GC51,GC52,GC53]
  requires pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
 case {
  curJob =null -> case {
    n3>0 -> ensures pq1'::ll1<n1,S11>*pq2'::ll1<n2,S21>*pq3'::ll1<n3-1,S31>*curJob'::node<v,v2,null> & res=curJob' & v2>=1 & v2<=3 
    & GC1(S3,S31,v) & GC11(S1,S11) & GC12(S2,S21);
    n3<=0 -> case {
      n2>0 -> ensures pq1'::ll1<n1,S11>*pq2'::ll1<n2-1,S21>*pq3'::ll1<n3,S31>*curJob'::node<v,v2,null> & res=curJob' & v2>=1 & v2<=3
    & GC2(S2,S21,v) & GC21(S1,S11) & GC22(S3,S31);
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll1<n1-1,S11>*pq2'::ll1<n2,S21>*pq3'::ll1<n3,S31>*curJob'::node<v,v2,null> & res=curJob' & v2>=1 & v2<=3 
    & GC1(S1,S11,v) & GC31(S2,S21) & GC32(S3,S31);
      n1<=0 -> ensures pq1'::ll1<n1,S11>*pq2'::ll1<n2,S21>*pq3'::ll1<n3,S31> & curJob'=null & res=null
    & GC41(S1,S11) & GC42(S2,S21) & GC43(S3,S31);
      }
    }
  }
  curJob !=null -> requires curJob::node<v1,v2,null>
  ensures pq1'::ll1<n1,S11>*pq2'::ll1<n2,S21>*pq3'::ll1<n3,S31>*curJob::node<v1,v2,null> &  curJob'=curJob& res=curJob
  & GC51(S1,S11) & GC52(S2,S21) & GC53(S3,S31);
}
{
    int prio;
    if(curJob == null)
      {
      node tmp = null;
      if(do_get_process1(1, curJob, pq3) > 0) return curJob;
      if(do_get_process1(1, curJob, pq2) > 0) return curJob;
      if(do_get_process1(1, curJob, pq1) > 0) return curJob;
    }
    return curJob;
}

 /* Put highest priority job into current_job */
int reschedule1(int prio, ref node cur_job, ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
 case{
  cur_job = null -> case {
    n3>0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3-1,S31>*cur_job'::node<v,v4,null> & v4>=1 & v4<=3 & res=0 & S3=union(S31,{v});
    n3<=0 -> case {
      n2>0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2-1,S21>*pq3'::ll1<n3,S3>*cur_job'::node<_,v4,null>  & v4>=1 & v4<=3 & res=0 & S2=union(S21,{v});
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll1<n1-1,S11>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3>*cur_job'::node<v,v4,null> & v4>=1 & v4<=3 & res=0 & S1=union(S11,{v});
        n1<=0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & cur_job'=null & res=0;
      }
    }
  }
  cur_job != null -> requires cur_job::node<v1,v2,null> & v2>=1 & v2 <=3 case {
    prio > v2 -> ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*cur_job'::node<v3,v4,null> & n4+n5+n6=n1+n2+n3 & res=0 & v4>=1 & v4<=3 ;
    prio <= v2 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3>*cur_job::node<v1,v2,null> & cur_job'=cur_job & res=0;
  }
}

int reschedule(int prio, ref node cur_job, ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
 case{
  cur_job = null -> case {
    n3>0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3-1,S31>*cur_job'::node<v,v4,null> & v4>=1 & v4<=3 & res=0 & S3=union(S31,{v});
    n3<=0 -> case {
      n2>0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2-1,S21>*pq3'::ll1<n3,S3>*cur_job'::node<_,v4,null>  & v4>=1 & v4<=3 & res=0 & S2=union(S21,{v}); 
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll1<n1-1,S11>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3>*cur_job'::node<v,v4,null> & v4>=1 & v4<=3 & res=0 & S1=union(S11,{v});
        n1<=0 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & cur_job'=null & res=0;
      }
    }
  }
  cur_job != null -> requires cur_job::node<v1,v2,null> & v2>=1 & v2 <=3 case {
    prio > v2 -> ensures pq1'::ll1<n4,S4>*pq2'::ll1<n5,S5>*pq3'::ll1<n6,S6>*cur_job'::node<v3,v4,null> & n4+n5+n6=n1+n2+n3 & res=0 & v4>=1 & v4<=3 ;
    prio <= v2 -> ensures pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3>*cur_job::node<v1,v2,null> & cur_job'=cur_job & res=0;
  }
}
{
    if(cur_job != null)
      {
      if (prio > cur_job.priority){
        node tmp = null;
        put_end1(cur_job.priority, cur_job, tmp,pq1,pq2,pq3);
        cur_job = null;//(struct process *)0;
      }
    }
    cur_job = get_current(cur_job, pq1, pq2, pq3); // Reschedule
    return 0;//OK 0
}

int schedule(int command, int prio, int ratio,ref node curJob,ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  requires pq0::ll1<n,S0>*pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3> & command >= 1 & command <= 7 & prio>=1 & prio<=3
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
      status = new_job1(prio, next_pid,curJob,pq1,pq2,pq3);
	}
	else if (command == 5) //QUANTUM_EXPIRE 5
	{
      status = quantum_expire1(curJob, pq0,pq1,pq2,pq3);
	}
	else if (command == 2) //UPGRADE_PRIO 2
	{
      status = upgrade_prio1(prio, ratio,curJob, pq1,pq2,pq3);
	}
	else if(command== 3) // BLOCK 3
	{
        status = block1(curJob,pq0,pq1,pq2,pq3);
	}
	else if (command == 4)// UNBLOCK 4
	{
      status = unblock1(ratio,curJob,pq0,pq1,pq2,pq3);
	}
	else if (command == 6)//FINISH :6
    {    finish1(curJob,pq1,pq2,pq3);
	}
	else if (command ==7)// FLUSH :7
	{
        status = flush1(curJob,pq1,pq2,pq3);
    }
	else status = -6;//NO_COMMAND -6;

    return status;
}

node lput_end1(node x, node y)
   requires y::node<v1,v2,null>
 case {
  x = null -> ensures y::node<v1,v2,null> & res = y;
  x != null -> requires x::ll1<n,S> ensures res::lseg1<y,n,S>*y::node<v1,v2,null>;
    }
{
  if (x==null)
    {
      return y;
    }
  node tmp=x.next;
  x.next=lput_end1(tmp,y);
  return x;
}


 /* Put process at end of queue */
int put_end1(int prio, node process, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  requires pq0::ll1<n,S0>*pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>*
  process::node<v1,v2,null> & v2>=1 & v2<=3
 case{
  prio = 0 -> ensures pq0'::lseg1<process,n,S01>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3>*process::node<v1,v2,null> & res = 0;
  prio = 1 -> requires v2=prio ensures pq0'::ll1<n,S0>*pq1'::lseg1<process,n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3>* process::node<v1,1,null> & res = 0;
  prio = 2 -> requires v2=prio ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::lseg1<process,n2,S2>*pq3'::ll1<n3,S3>*process::node<v1,2,null> & res = 0;
  prio = 3 -> requires v2=prio ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::lseg1<process,n3,S3>*process::node<v1,3,null> & res = 0;
  prio > 3 | prio < 0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3>*process::node<v1,v2,null> & res = -4;
 }
{
    node next;
    if(prio > 3 || prio < 0) return (-4); /* Somebody goofed MAXPRIO 3 BADPRIO -4*/
     /* find end of queue */
    if (prio == 0)
      pq0 = lput_end1(pq0, process);
    else if (prio == 1)
      pq1 = lput_end1(pq1, process);
    else if (prio == 2)
      pq2 = lput_end1(pq2, process);
    else if (prio == 3)
      pq3 = lput_end1(pq3, process);
    return (0);//OK 0
}

node del_ele1(ref node x, node ele)
  requires (exists j,q: x::lseg1<ele,j,S1> * ele::node<v1,v2,q> * q::ll1<m,S2>) 
  ensures x'::lseg1<q,j,S1> * q::ll1<m,S2> * ele::node<v1,v2,q>& v2 >=0 & v2 <= 3 & res=x';

node find_nth1(node f_list, int j)
  requires j>=1
 case {
  f_list!=null -> requires f_list::ll1<n,S> & j<=n
    ensures (exists q: f_list::lseg1<res,j-1,S1> * res::node<v1,v2,q> * q::ll1<n-j,S2> & v2>=1 & v2<=3 & S=union(S1,{v1},S2));
  f_list = null -> ensures f_list=null & res=null;
}

int do_get_process1(int ratio, ref node job, ref node pq0)
  requires pq0::ll1<n,S>
 case {
  ratio < 1 | ratio > n -> ensures pq0'::ll1<n,S> & res=-5 & job'=job;
  ratio >= 1 & ratio <= n -> case{
    n = 0 -> ensures pq0'=null & job'=null & res = 0;
    n != 0 -> ensures pq0'::ll1<n-1,S1> * job'::node<v,v4,null> & res = 1 & v4>=1 & v4<=3 & S=union(S1,{v});
  }
}

int do_get_process(int ratio, ref node job, ref node pq0)
  requires pq0::ll1<n,S>
 case {
  ratio < 1 | ratio > n -> ensures pq0'::ll1<n,S> & res=-5 & job'=job;
  ratio >= 1 & ratio <= n -> case{
    n = 0 -> ensures pq0'=null & job'=null & res = 0;
    n != 0 -> ensures pq0'::ll1<n-1,S1> * job'::node<v,v4,null> & res = 1 & v4>=1 & v4<=3 & S=union(S1,{v});
  }
}
{
  int length;
  int index;
  length = get_mem_count1(pq0);
  if(ratio < 1 || ratio > length) return (-5); /* Somebody else goofed BADRATIO -5*/
  index = ratio ;//* length;

  job = find_nth1(pq0, index);//index

  if(job != null)
    {
      pq0 = del_ele1(pq0, job);
      job.next = null;
      return 1;//TRUE 1
    }
  else return 0;//FALSE 0
}


int get_process1(int prio, int ratio, ref node job, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  requires pq0::ll1<n,S0>*pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
 case {
  prio = 0 -> case {
    ratio < 1 | ratio > n -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-5;
    ratio >= 1 & ratio <= n -> case{
      n = 0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & job'=null & res = 0;
      n != 0 -> ensures pq0'::ll1<n-1,S01>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> * job'::node<v,v4,null> & v4>=1 & v4<=3 & res = 1 & S0=union(S01,{v});
      }
    }
    prio = 1 -> case {
      ratio < 1 | ratio > n1 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-5;
      ratio >= 1 & ratio <= n1 -> case{
        n1 = 0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & job'=null & res = 0;
      n1 != 0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1-1,S11>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> * job'::node<v,v4,null> & v4>=1 & v4<=3 & res = 1 & S1=union(S11,{v});
      }
    }
    prio = 2 -> case {
      ratio < 1 | ratio > n2 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-5;
      ratio >= 1 & ratio <= n2 -> case{
        n2 = 0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & job'=null & res = 0;
      n2 != 0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2-1,S21>*pq3'::ll1<n3,S3> * job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1 & S2=union(S21,{v});
      }
    }
    prio = 3 -> case {
      ratio < 1 | ratio > n3 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-5;
      ratio >= 1 & ratio <= n3 -> case{
      n3 = 0 -> ensures  pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & job'=null & res = 0;
      n3 != 0 -> ensures  pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3-1,S31>* job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1 & S3=union(S31,{v});
      }
    }
    prio > 3 | prio <0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-4;
}

relation GP0(bag a, bag b, int c).
relation GP1(bag a, bag b, int c).
relation GP2(bag a, bag b, int c).
relation GP3(bag a, bag b, int c).
relation GP01(bag a, bag b).
relation GP02(bag a, bag b).
relation GP03(bag a, bag b).
relation GP11(bag a, bag b).
relation GP12(bag a, bag b).
relation GP13(bag a, bag b).
relation GP21(bag a, bag b).
relation GP22(bag a, bag b).
relation GP23(bag a, bag b).
relation GP31(bag a, bag b).
relation GP32(bag a, bag b).
relation GP33(bag a, bag b).
int get_process(int prio, int ratio, ref node job, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  infer [GP0,GP1,GP2,GP3,GP01,GP02,GP03,GP11,GP12,GP13,GP21,GP22,GP23,GP31,GP32,GP33]
  requires pq0::ll1<n,S0>*pq1::ll1<n1,S1>*pq2::ll1<n2,S2>*pq3::ll1<n3,S3>
 case {
  prio = 0 -> case {
    ratio < 1 | ratio > n -> ensures pq0'::ll1<n,S01>*pq1'::ll1<n1,S11>*pq2'::ll1<n2,S21>*pq3'::ll1<n3,S31> & res=-5;
    ratio >= 1 & ratio <= n -> case{
      n = 0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & job'=null & res = 0;
      n != 0 -> ensures pq0'::ll1<n-1,S01>*pq1'::ll1<n1,S11>*pq2'::ll1<n2,S21>*pq3'::ll1<n3,S31> * job'::node<v,v4,null> & v4>=1 & v4<=3 & res = 1 
      & GP0(S0,S01,v) & GP01(S1,S11) & GP02(S2,S21) & GP03(S3,S31);
      }
    }
    prio = 1 -> case {
      ratio < 1 | ratio > n1 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-5;
      ratio >= 1 & ratio <= n1 -> case{
        n1 = 0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & job'=null & res = 0;
        n1 != 0 -> ensures pq0'::ll1<n,S01>*pq1'::ll1<n1-1,S11>*pq2'::ll1<n2,S21>*pq3'::ll1<n3,S31> * job'::node<v,v4,null> & v4>=1 & v4<=3 & res = 1 
        & GP1(S1,S11,v) & GP11(S0,S01) & GP12(S2,S21) & GP13(S3,S31);
      }
    }
    prio = 2 -> case {
      ratio < 1 | ratio > n2 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-5;
      ratio >= 1 & ratio <= n2 -> case{
        n2 = 0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & job'=null & res = 0;
        n2 != 0 -> ensures pq0'::ll1<n,S01>*pq1'::ll1<n1,S11>*pq2'::ll1<n2-1,S21>*pq3'::ll1<n3,S31> * job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1
        & GP2(S2,S21,v) & GP21(S0,S01) & GP22(S1,S11) & GP23(S3,S31);
      }
    }
    prio = 3 -> case {
      ratio < 1 | ratio > n3 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-5;
      ratio >= 1 & ratio <= n3 -> case{
      n3 = 0 -> ensures  pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & job'=null & res = 0;
      n3 != 0 -> ensures  pq0'::ll1<n,S01>*pq1'::ll1<n1,S11>*pq2'::ll1<n2,S21>*pq3'::ll1<n3-1,S31>* job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1 
      & GP3(S3,S31,v) & GP31(S0,S01) & GP32(S1,S11) & GP33(S2,S21);
      }
    }
    prio > 3 | prio <0 -> ensures pq0'::ll1<n,S0>*pq1'::ll1<n1,S1>*pq2'::ll1<n2,S2>*pq3'::ll1<n3,S3> & res=-4;
}
{
  int status;
  if(prio > 3 || prio < 0) return (-4); /* Somebody goofed MAXPRIO 3, BADPRIO -4*/
    else {
      if (prio == 0) status = do_get_process1(ratio, job, pq0);
      else if (prio == 1) status = do_get_process1(ratio, job, pq1);
      else if (prio == 2) status = do_get_process1(ratio, job, pq2);
      else if (prio == 3) status = do_get_process1(ratio, job, pq3);

      return status;
    }
}

