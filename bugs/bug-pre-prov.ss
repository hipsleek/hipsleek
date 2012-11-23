data node {
	int val;
    int priority;
    node next;
}

ll<n> == self=null & n=0
  or self::node<_, _, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
  or self::node<_,_, q> * q::lseg<p, n-1>
	inv n>=0;


node find_nth2(node f_list, int j)
	requires f_list::ll<n> & j>=1 & n>=1
	case {
		j <= n -> ensures f_list::lseg<res,j-1> * res::node<_,v2,q> * q::ll<n-j> & v2>=1 & v2<=3;
		j > n -> ensures f_list::ll<n> & res=null;
  }

void upgrade_process_prio( ref node pq1, ref node pq2)
	requires pq1::ll<n1> * pq2::ll<n2> 
	case {
  pq1 != null -> ensures pq1'::ll<n1-1> * pq2'::ll<n2+1>;
  pq1 = null -> ensures pq2'::ll<n2>  & pq1'=null;
  }
{
	node proc = find_nth2(pq1,0);
}
