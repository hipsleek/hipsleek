data node{
    int id;
    int priority;
    node next;
}

ll<n> == self=null & n=0
  or self::node<_, _, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
  or self::node<_,_, q> * q::lseg<p, n-1>
	inv n>=0;

lemma self::ll<n> <-> self::lseg<null,n>;
lemma "V1" self::lseg<p,n> & n = a + b & a,b >=0 <-> self::lseg<r,a> * r::lseg<p,b>;


int get_mem_count(node x)
  requires x::ll<n>
  ensures x::ll<n> & res=n;

global node current_job;
global int next_pid;
global node prio_queue0;/* blocked queue is [0] */
global node prio_queue1;
global node prio_queue2;
global node prio_queue3;

int enqueue(int prio, node new_process,ref node curJob,ref node pq0, ref node pq1,
            ref node pq2, ref node pq3)
  requires pq0::ll<n>*pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>*new_process::node<v1,v2,null>
  & v2>=1 & v2<=3
 case{
  prio = 0 -> case {
    curJob = null -> case{
      n1+n2+n3>0 ->
      ensures pq0'::lseg<new_process,n>*pq1'::ll<n4>*pq2'::ll<n5>*
      pq3'::ll<n6>*new_process::node<_,v2,null>*curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3-1 & v4>=1 & v4<=3 &res = 0;
      n1+n2+n3<=0 ->
      ensures pq0'::lseg<new_process,n>*pq1'::ll<n1>*pq2'::ll<n2>*
      pq3'::ll<n3>* new_process::node<_,v2,null> & v4>=1 & v4<=3 & curJob'=null & res = 0;
    }
   curJob != null ->requires curJob::node<v3,v,null>& v>=1 & v<=3
     ensures pq0'::lseg<new_process,n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*
    new_process::node<v1,v2,null>*curJob::node<v3,v,null> & curJob'=curJob & res = 0;
  }
 prio >= 1 & prio<=3 -> case {
    curJob = null -> requires v2=prio
      ensures pq0'::ll<n>*pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*curJob'::node<_,v4,null>
*new_process::node<v1,v2,null> & n4+n5+n6=n1+n2+n3 & v4>=1 & v4<=3 & res = 0;
    curJob != null -> requires curJob::node<_,v,null> & v2=prio & v>=1 & v<=3
    ensures pq0'::ll<n>*pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*curJob'::node<_,v5,null>*
new_process::node<v1,v2,null> & n4+n5+n6=n1+n2+n3+1 &v5>=1 & v5<=3 & res = 0;
  }
  prio > 3 | prio < 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*
    new_process::node<v1,v2,null> & res = -4;
 }

int enqueue1(int prio, node new_process,ref node curJob,ref node pq0, ref node pq1,
            ref node pq2, ref node pq3)
  requires pq0::ll<n>*pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>*new_process::node<v1,v2,null>
  & v2>=1 & v2<=3
 case{
  prio = 0 -> case {
    curJob = null -> case{
      n1+n2+n3>0 -> 
      ensures pq0'::lseg<new_process,n>*pq1'::ll<n4>*pq2'::ll<n5>*
      pq3'::ll<n6>*new_process::node<_,v2,null>*curJob'::node<_,_,null>;
      n1+n2+n3<=0 -> 
      ensures pq0'::lseg<new_process,n>*pq1'::ll<n1>*pq2'::ll<n2>*
      pq3'::ll<n3>* new_process::node<_,v2,null>;
    }
   curJob != null ->requires curJob::node<v3,v,null>& v>=1 & v<=3
     ensures pq0'::lseg<new_process,n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*
    new_process::node<v1,v2,null>*curJob::node<v3,v,null> ;
  }
  prio >= 1 & prio<=3 -> case {
    curJob = null -> requires v2=prio
      ensures pq0'::ll<n>*pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
      curJob'::node<_,v4,null> ;
    curJob != null -> requires curJob::node<_,v,null> & v2=prio & v>=1 & v<=3
    ensures pq0'::ll<n>*pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
      curJob'::node<_,v4,null> ;
  }
  prio > 3 | prio < 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*
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
requires  pq0::ll<n>*pq1::ll<n1> * pq2::ll<n2> * pq3::ll<n3> & next_pid=0 & curJob=null
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
int new_job(int prio,ref int npid,ref node curJob,ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3> & prio>=1 & prio<=3
case {
  prio = 0 -> ensures true; 
  prio >= 1 & prio<=3 -> case{
    curJob = null -> ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
      curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3 & npid'=npid +1 & res = 0;
    curJob != null ->requires curJob::node<_,v,null> & v>=1 & v<=3
      ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6> *curJob'::node<_,v3,null>
      & n4+n5+n6=n1+n2+n3+1 & npid'=npid +1 &res = 0;
  }
  prio > 3 | prio < 0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & npid'=npid &res = -4;
 }

relation NJ1(int a, int b, int c, int d, int e, int f).
relation NJ2(int a, int b, int c).
relation NJ3(int a, int b, int c, int d, int e, int f).
relation NJ4(int a, int b, int c).
int new_job1(int prio,ref int npid,ref node curJob,ref node pq1, ref node pq2, ref node pq3)
  infer [NJ1,NJ2,NJ3,NJ4]
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3> & prio>=1 & prio<=3
  case {
  prio = 0 -> ensures true; 
  prio >= 1 & prio<=3 -> 
    case
    {
    curJob = null -> ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
    curJob'::node<_,_,null> & NJ1(n1,n2,n3,n4,n5,n6) & NJ2(npid',npid,res); 
    curJob != null ->
      requires curJob::node<_,v,null> & v>=1 & v<=3
      ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6> *curJob'::node<_,v3,null> 
      & NJ3(n1,n2,n3,n4,n5,n6) & NJ4(npid',npid,res);
    }
  prio > 3 | prio < 0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>;
  }
{
  int status = 0;//OK 0
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
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
  case{
    prio = 1 -> case {
      ratio < 1 | ratio > n1 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res=-5;	 
      ratio >= 1 & ratio <= n1 ->  case {
	n1 = 0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res = 0;
	n1 != 0 -> case {
	  curJob = null -> ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
            curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3-1 & res=0;
	  curJob != null -> requires curJob::node<_,v,null>& v>=1 & v<=3
	   ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
            curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3 & res=0;
	}
      }
    }
    prio = 2 -> case {
      ratio < 1 | ratio > n2 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res=-5;
      ratio >= 1 & ratio <= n2 ->  case {
	n2 = 0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res = 0;
	n2 != 0 ->case {
	  curJob = null -> ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
            curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3-1 & res=0;
	  curJob != null -> requires curJob::node<_,v,null>& v>=1 & v<=3
	   ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
            curJob'::node<_,_,null> & n4+n5+n6=n1+n2+n3 & res=0;
	}
      }
    }
    prio > 2 | prio <1 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res=-4;
  }

relation UP1(int a, int b, int c, int d, int e, int f, int res1).
relation UP2(int a, int b, int c, int d, int e, int f, int res1).
relation UP3(int a).
relation UP4(int a, int b, int c, int d, int e, int f, int res1).
relation UP5(int a, int b, int c, int d, int e, int f, int res1).
relation UP6(int a).
relation UP7(int a).
relation UP8(int a).
int upgrade_prio1(int prio,int ratio,ref node curJob,ref node pq1,ref node pq2,ref node pq3)
  infer [UP1,UP2,UP3,UP4,UP5,UP6,UP7,UP8]
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
  case {
    prio = 1 -> 
      case {
      ratio < 1 | ratio > n1 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>;
      ratio >= 1 & ratio <= n1 ->  
        case {
        n1 = 0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & UP3(res);
        n1 != 0 -> 
          case {
	        curJob = null -> 
            ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
            curJob'::node<_,_,null> & UP1(n1,n2,n3,n4,n5,n6,res);
	        curJob != null -> 
            requires curJob::node<_,v,null>& v>=1 & v<=3
	          ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
            curJob'::node<_,_,null> & UP2(n1,n2,n3,n4,n5,n6,res);
	        }
        }
      }
    prio = 2 -> 
      case {
      ratio < 1 | ratio > n2 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & UP6(res);
      ratio >= 1 & ratio <= n2 -> 
        case {
        n2 = 0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & UP7(res);
        n2 != 0 ->
          case {
          curJob = null -> 
            ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
            curJob'::node<_,_,null> & UP4(n1,n2,n3,n4,n5,n6,res);
	        curJob != null -> 
            requires curJob::node<_,v,null>& v>=1 & v<=3
	          ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
            curJob'::node<_,_,null> & UP5(n1,n2,n3,n4,n5,n6,res);
	        }
        }
      }
    prio > 2 | prio < 1 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & UP8(res);
  }
{
  int status;
  node job, tmp;
  tmp = null;
  if(prio < 1 || prio > 2) 
    return (-4);//MAXLOPRIO 2; BADPRIO -4
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
 requires pq0::ll<n>*pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
 case { curJob=null -> ensures true;
   curJob!=null -> requires curJob::node<_,v2,null> & v2>=1 & v2<=3 ensures true;
}

int block1(ref node curJob, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  requires pq0::ll<n>*pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
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
    curJob = null;//(struct process *)0; // remove it
    return (enqueue(0, job,curJob, pq0,pq1,pq2,pq3));
  // BLOCKPRIO 0 put into blocked queue 
  }
  return 0;//OK 0
}

/* Restore job @ ratio in blocked queue to its queue */
int unblock(int ratio,ref node curJob, ref node pq0,ref node pq1, ref node pq2, ref node pq3)
  requires pq0::ll<n>*pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
 case {
   ratio  < 1 | ratio > n -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res=-5;
    ratio >= 1 & ratio <= n -> case{
      n=0 -> ensures  pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res=0;
      n!=0 -> case {
	curJob = null -> ensures pq0'::ll<n-1>*pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
	  curJob'::node<_,v4,null> & res=0 & n4+n5+n6=n1+n2+n3 & v4>=1 & v4<=3;
        curJob != null -> requires curJob::node<_,v,null> & v>=1 & v<=3
	   ensures pq0'::ll<n-1>*pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
	  curJob'::node<_,v4,null> & res=0 & n4+n5+n6=n1+n2+n3+1 & v4>=1 & v4<=3;
      }

    }
}

relation UB1(int a, int b, int c, int d, int e, int f, int res1, int g).
relation UB2(int a, int b, int c, int d, int e, int f, int res1, int g).
relation UB3(int a).
relation UB4(int a).
int unblock1(int ratio,ref node curJob, ref node pq0,ref node pq1, ref node pq2, ref node pq3)
  infer [UB1,UB2,UB3,UB4]
  requires pq0::ll<n>*pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
  case {
    ratio < 1 | ratio > n -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & UB3(res);
    ratio >= 1 & ratio <= n -> 
      case {
      n=0 -> ensures  pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & UB4(res);
      n!=0 -> 
        case {
        curJob = null -> ensures pq0'::ll<n-1>*pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
	      curJob'::node<_,v4,null> & UB1(n1,n2,n3,n4,n5,n6,res,v4);
        curJob != null -> 
          requires curJob::node<_,v,null> & v>=1 & v<=3
          ensures pq0'::ll<n-1>*pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
	        curJob'::node<_,v4,null> & UB2(n1,n2,n3,n4,n5,n6,res,v4);
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
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
 case {
  curJob = null -> case {
    n1+n2+n3>0 -> ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*curJob'::node<_,v4,null>
    & res=0 & n4+n5+n6=n1+n2+n3-1 & v4>=1 & v4<=3;
    n1+n2+n3<=0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res=0 & curJob'=null;
  }
  curJob != null -> requires curJob::node<v1,v2,null> & v2>=1 & v2<=3
    ensures  pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*curJob'::node<_,v4,null>
    & res=0 & n4+n5+n6=n1+n2+n3 & v4>=1 & v4<=3;
  }

relation QE1(int a, int b, int c, int d, int e, int f, int res1, int g).
relation QE2(int a, int b, int c, int d, int e, int f, int res1, int g).
relation QE3(node a, int b).
int quantum_expire1(ref node curJob,ref node pq1, ref node pq2, ref node pq3)
  infer [QE1,QE2,QE3]
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
 case {
  curJob = null -> case {
    n1+n2+n3>0 -> ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*curJob'::node<_,v4,null> & QE1(n1,n2,n3,n4,n5,n6,res,v4);
    n1+n2+n3<=0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & QE3(curJob',res);
  }
  curJob != null -> requires curJob::node<v1,v2,null> & v2>=1 & v2<=3
  ensures  pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*curJob'::node<_,v4,null>& QE2(n1,n2,n3,n4,n5,n6,res,v4);
  }
{
  node  job, tmp;
    int status;
    job = get_current(curJob, pq1, pq2, pq3);
    if(job != null)
    {
      curJob = null;//(struct process *)0; /* remove it */
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
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
   case {
  curJob =null -> case {
    n1=0 & n2=0 & n3=0 ->  ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> &
    curJob' = null  & res=1;
    n1!=0 | n2!=0 | n3!=0 -> ensures res=0;
  }
  curJob !=null -> requires curJob::node<_,_,null> case {
    n1+n2+n3>=1 -> ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
      curJob'::node<_,_,null> & res=0 & n4+n5+n6=n1+n2+n3-1;
    (n1+n2+n3)<1 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>
      & curJob'=null & res=0;
  }
}

relation FI1(int a, int b, int c, int d, int e, int f, int res1).
  relation FI2(int a).
  relation FI3(node a, int b).
relation FI4(node a, int b).
int finish1(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
  infer [FI1,FI2,FI3,FI4] 
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
   case {
  curJob =null -> case {
    n1=0 & n2=0 & n3=0 ->  ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & FI3(curJob',res);
  n1!=0 | n2!=0 | n3!=0 -> ensures FI2(res);
  }
  curJob !=null -> requires curJob::node<_,_,null> case {
    n1+n2+n3>=1 -> ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*
      curJob'::node<_,_,null> & FI1(n1,n2,n3,n4,n5,n6,res);
    (n1+n2+n3)<1 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & FI4(curJob',res);
  }
}
{
    node job;
    job = get_current(curJob, pq1, pq2, pq3);
    if(job != null)
    {
	  curJob = null;//(struct process *)0;
	  reschedule(0, curJob,pq1,pq2,pq3);
      free(job);
	  return 0; //FALSE 0
    }
    else return 1;//TRUE 1
}

/* Get all jobs in priority queues & zap them */
int flush(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
 case {
  curJob = null & n1=0 & n2=0 & n3=0 -> ensures pq1'=null & pq2'=null & pq3'=null &
  curJob' = null & res=0;
  curJob != null | n1!=0 | n2!=0 | n3!=0 -> requires curJob::node<_,_,null>
  ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6> &
      n4+n5+n6<=n1+n2+n3 & res=0;
}

relation FLU1(int a, int b, int c, int d, int e, int f, int res1).
relation FLU2(node a, node b, node c, node d, int f).
int flush1(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
  infer [FLU1,FLU2]
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
 case {
  curJob = null & n1=0 & n2=0 & n3=0 -> ensures FLU2(pq1', pq2',pq3',curJob',res);
  curJob != null | n1!=0 | n2!=0 | n3!=0 -> requires curJob::node<_,_,null>
  ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6> & FLU1(n1,n2,n3,n4,n5,n6,res);
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
   requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
  case {
  curJob =null -> case {
    n3>0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3-1>*curJob'::node<_,v2,null> & res=curJob' & v2>=1 & v2<=3;
    n3<=0 -> case {
      n2>0 -> ensures pq1'::ll<n1>*pq2'::ll<n2-1>*pq3'::ll<n3>*curJob'::node<_,v2,null> & res=curJob' & v2>=1 & v2<=3;
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll<n1-1>*pq2'::ll<n2>*pq3'::ll<n3>*curJob'::node<_,v2,null> & res=curJob' & v2>=1 & v2<=3;
        n1<=0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & curJob'=null & res=null;
      }
    }
  }
  curJob !=null -> requires curJob::node<v1,v2,null>
    ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*curJob::node<v1,v2,null> &  curJob'=curJob& res=curJob;
}

relation GC1(node a, int b).
relation GC2(node a, int b).
relation GC3(node a, int b).
relation GC4(node a, node b).
  relation GC5(node a, node b, node c).
node get_current1(ref node curJob, ref node pq1, ref node pq2, ref node pq3)
  infer [GC1,GC2,GC3,GC4,GC5]
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
 case {
  curJob =null -> case {
    n3>0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3-1>*curJob'::node<_,v2,null> & GC1(res,v2);
    n3<=0 -> case {
      n2>0 -> ensures pq1'::ll<n1>*pq2'::ll<n2-1>*pq3'::ll<n3>*curJob'::node<_,v2,null> & GC2(res,v2);
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll<n1-1>*pq2'::ll<n2>*pq3'::ll<n3>*curJob'::node<_,v2,null> & GC3(res,v2);
        n1<=0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & GC4(curJob',res);
      }
    }
  }
  curJob !=null -> requires curJob::node<v1,v2,null>
  ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*curJob::node<v1,v2,null> & GC5(curJob',res, curJob);
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
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
   case{
  cur_job = null -> case {
    n3>0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3-1>*cur_job'::node<_,v4,null> & v4>=1 & v4<=3 & res=0;
    n3<=0 -> case {
      n2>0 -> ensures pq1'::ll<n1>*pq2'::ll<n2-1>*pq3'::ll<n3>*cur_job'::node<_,v4,null>  & v4>=1 & v4<=3 & res=0;
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll<n1-1>*pq2'::ll<n2>*pq3'::ll<n3>*cur_job'::node<_,v4,null> & v4>=1 & v4<=3 & res=0;
        n1<=0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & cur_job'=null & res=0;
      }
    }
  }
  cur_job != null -> requires cur_job::node<v1,v2,null> & v2>=1 & v2 <=3 case {
    prio > v2 -> ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*cur_job'::node<_,v4,null> & n4+n5+n6=n1+n2+n3 & res=0 & v4>=1 & v4<=3;
   prio <= v2 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*cur_job::node<v1,v2,null> & cur_job'=cur_job & res=0;
  }
}

relation RESC1(int a, int b).
relation RESC2(int a, int b).
relation RESC3(int a, int b).
relation RESC4(node a, int b).
  relation RESC5(node a, node c, int b).
  relation RESC6(int a, int b, int c, int d, int e, int f, int g, int h).
int reschedule1(int prio, ref node cur_job, ref node pq1, ref node pq2, ref node pq3)
  infer [RESC1,RESC2,RESC3,RESC4,RESC5,RESC6]
  requires pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
 case{
  cur_job = null -> case {
    n3>0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3-1>*cur_job'::node<_,v4,null> & RESC1(res,v4);
    n3<=0 -> case {
      n2>0 ->ensures pq1'::ll<n1>*pq2'::ll<n2-1>*pq3'::ll<n3>*cur_job'::node<_,v4,null> & RESC2(res,v4);
      n2<=0 -> case{
        n1>0 -> ensures pq1'::ll<n1-1>*pq2'::ll<n2>*pq3'::ll<n3>*cur_job'::node<_,v4,null> & RESC3(res,v4);
        n1<=0 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & RESC4(cur_job',res);
      }
    }
  }
  cur_job != null -> requires cur_job::node<v1,v2,null> & v2>=1 & v2 <=3 case {
    prio > v2 -> ensures pq1'::ll<n4>*pq2'::ll<n5>*pq3'::ll<n6>*cur_job'::node<_,v4,null> & RESC6(n1,n2,n3,n4,n5,n6,res,v4);
    prio <= v2 -> ensures pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*cur_job::node<v1,v2,null> & RESC5(cur_job,cur_job',res);
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
    requires pq0::ll<n>*pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3> & command >= 1 & command <= 7 & prio>=1 & prio<=3
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
  x != null -> requires x::ll<n> ensures res::lseg<y,n>*y::node<v1,v2,null>;
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
  requires pq0::ll<n>*pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>*process::node<v1,v2,null>
   &v2>=1 & v2<=3
 case{
   prio = 0 -> ensures pq0'::lseg<process,n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*process::node<v1,v2,null> & res = 0;
   prio = 1 -> requires v2=prio ensures pq0'::ll<n>*pq1'::lseg<process,n1>*pq2'::ll<n2>*pq3'::ll<n3>* process::node<v1,v2,null> & res = 0;
   prio = 2 -> requires v2=prio ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::lseg<process,n2>*pq3'::ll<n3>*process::node<v1,v2,null> & res = 0;
   prio = 3 -> requires v2=prio ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::lseg<process,n3>*process::node<v1,v2,null> & res = 0;
   prio > 3 | prio < 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*
   process::node<v1,v2,null> & res = -4;
 }

relation PE1(int a).
relation PE2(int a).
relation PE3(int a).
relation PE4(int a).
relation PE5(int a).
 int put_end1(int prio, node process, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  infer [PE1,PE2,PE3,PE4,PE5]
  requires pq0::ll<n>*pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>*process::node<v1,v2,null>
   &v2>=1 & v2<=3
 case{
  prio = 0 -> ensures pq0'::lseg<process,n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*process::node<v1,v2,null> & PE1(res);
   prio = 1 -> requires v2=prio ensures pq0'::ll<n>*pq1'::lseg<process,n1>*pq2'::ll<n2>*pq3'::ll<n3>* process::node<v1,v2,null>& PE3(res);
   prio = 2 -> requires v2=prio ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::lseg<process,n2>*pq3'::ll<n3>*process::node<v1,v2,null> & PE3(res);
   prio = 3 -> requires v2=prio ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::lseg<process,n3>*process::node<v1,v2,null> & PE4(res);
   prio > 3 | prio < 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>*
     process::node<v1,v2,null> & PE5(res);
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
  requires (exists j,q: x::lseg<ele,j> * ele::node<v1,v2,q> * q::ll<m>)
  ensures x'::lseg<q,j> * q::ll<m> * ele::node<v1,v2,q>& v2 >=0 & v2 <= 3 & res=x';

node find_nth(node f_list, int j)
  requires j>=1
 case {
  f_list!=null -> requires f_list::ll<n> & j<=n
    ensures (exists q: f_list::lseg<res,j-1> * res::node<_,v2,q> * q::ll<n-j> & v2>=1 & v2<=3);
  f_list = null -> ensures f_list=null & res=null;
}

int do_get_process(int ratio, ref node job, ref node pq0)
  requires pq0::ll<n>
 case {
  ratio < 1 | ratio > n -> ensures pq0'::ll<n> & res=-5 & job'=job;
  ratio >= 1 & ratio <= n -> case{
    n = 0 -> ensures pq0'=null & job'=null & res = 0;
    n != 0 -> ensures pq0'::ll<n-1> * job'::node<_,v4,null> & res = 1 & v4>=1 & v4<=3;
  }
}
{
  int length;
  int index;
  length = get_mem_count(pq0);
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
  requires pq0::ll<n>*pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
 case {
    prio = 0 -> case {
      ratio < 1 | ratio > n -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res=-5;
      ratio >= 1 & ratio <= n -> case{
      n = 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & job'=null & res = 0;
      n != 0 -> ensures pq0'::ll<n-1>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> * job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1;
      }
    }
    prio = 1 -> case {
      ratio < 1 | ratio > n1 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res=-5;
      ratio >= 1 & ratio <= n1 -> case{
      n1 = 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & job'=null & res = 0;
      n1 != 0 -> ensures pq0'::ll<n>*pq1'::ll<n1-1>*pq2'::ll<n2>*pq3'::ll<n3> * job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1;
      }
    }
    prio = 2 -> case {
      ratio < 1 | ratio > n2 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res=-5;
      ratio >= 1 & ratio <= n2 -> case{
      n2 = 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & job'=null & res = 0;
      n2 != 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2-1>*pq3'::ll<n3> * job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1;
      }
    }
    prio = 3 -> case {
      ratio < 1 | ratio > n3 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res=-5;
      ratio >= 1 & ratio <= n3 -> case{
      n3 = 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & job'=null & res = 0;
      n3 != 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3-1> * job'::node<_,v4,null> & v4>=1 & v4<=3 & res = 1;
      }
    }
    prio > 3 | prio <0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & res=-4;
}

relation GP1(int a).
relation GP2(node a, int b).
relation GP3(int a, int b).
relation GP4(int a).
int get_process1(int prio, int ratio, ref node job, ref node pq0, ref node pq1, ref node pq2, ref node pq3)
  infer [GP1, GP2, GP3,GP4]
  requires pq0::ll<n>*pq1::ll<n1>*pq2::ll<n2>*pq3::ll<n3>
 case {
    prio = 0 -> case {
      ratio < 1 | ratio > n -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & GP1(res);
      ratio >= 1 & ratio <= n -> case{
        n = 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & GP2(job', res);
      n != 0 -> ensures pq0'::ll<n-1>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> * job'::node<_,v4,null> & GP3(v4,res);
      }
    }
    prio = 1 -> case {
      ratio < 1 | ratio > n1 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & GP1(res);
      ratio >= 1 & ratio <= n1 -> case{
      n1 = 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>& GP2(job', res);
      n1 != 0 -> ensures pq0'::ll<n>*pq1'::ll<n1-1>*pq2'::ll<n2>*pq3'::ll<n3> * job'::node<_,v4,null>& GP3(v4,res);
      }
    }
    prio = 2 -> case {
      ratio < 1 | ratio > n2 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & GP1(res);
      ratio >= 1 & ratio <= n2 -> case{
      n2 = 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>& GP2(job', res);
      n2 != 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2-1>*pq3'::ll<n3> * job'::node<_,v4,null>& GP3(v4,res);
      }
    }
    prio = 3 -> case {
      ratio < 1 | ratio > n3 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>& GP1(res);
      ratio >= 1 & ratio <= n3 -> case{
      n3 = 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3>& GP2(job', res);
      n3 != 0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3-1> * job'::node<_,v4,null>& GP3(v4,res);
      }
    }
    prio > 3 | prio <0 -> ensures pq0'::ll<n>*pq1'::ll<n1>*pq2'::ll<n2>*pq3'::ll<n3> & GP4(res);
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
