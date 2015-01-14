data node {
	int val;
	node next;
}

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;
/*
ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

clist<n> == self::node<_,p> * p::lseg<self,n-1>
	inv n>=1;
*/

void append(node x, node y)
  requires x::lseg<r, n> * r::node<b,null>
  ensures x::lseg<r,n> * r::node<b,y>;
{
  // dprint;
	node tmp = x.next;
	bool fl = tmp != null;
	if (fl) {
		append(x.next, y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}

/*
test/append.ss --eps --eci

Exception Failure("view is unlabeled\n") Occurred!
(Program not linked with -g, cannot print stack backtrace)

I guess "false need to be labelled?"
What is this label for for --eps?

  ECase case {
         n=0 -> :EBase {178}->emp&(([n=0][p=self]))&{FLOW,(1,27)=__flow}[] ;
         1<=n -> :EBase exists (Expl)[](Impl)[_; q](ex)[]{179}->(exists p_23,
                        flted_7_22: self::node<_,q>@M@ rem br[{1}] * 
                        q::lseg<p_23,flted_7_22>@M@ rem br[{178,179}]&(
                        ([n=1+flted_7_22][p=p_23][true]))&
                        {FLOW,(1,27)=__flow})[]
         ;
         n<=(0-1) -> EBase hfalse&(([false]))&{FLOW,(0,0)=__false}[] 
         }

*/
