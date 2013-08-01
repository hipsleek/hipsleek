data node{
	int val;
	node prev;
	node next;
}

node foo (node c)
  requires c::node<a,b,n>
  ensures c::node<a,b,res> & res=n;
{
    node t = c.next;
    dprint;
    return t;
}

/*
../../hip ltail.ss --field-ann

Checking procedure foo$node... 
!!! Andreea : we need to normalise struc_vheap
!!! ==========================================
!!! struc_vheap: EBase c'::node<val_11_764'@A,prev_11_765'@A,next_11_766'@L>@L[Orig]&true&
       {FLOW,(1,25)=__flow}[]

*/

