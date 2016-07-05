data node{
	int val;
	node next;
}


lx<g,s,"S":M> == true & ["":self=g & self!=s; "S": M={}]
  or self::node<v,nxt> * nxt::lx<g,s,M1> & ["":self!=g & self!=s; "S": M=union(M1,{self})]
inv self!=s
;
//true & ["n":self!=s]  

void lscan(ref node cur, ref node prev, node sent)
 requires cur::lx<a,b,M1> * prev::lx<b,a,M2> & ["":cur!=a & (a=null & b=sent | a=sent & b=null)]
 ensures prev'::lx<c,sent,union(M1,M2)>  & ["":c=null & cur'=sent];

{

  node n;
  n = cur.next;
  // rotate ptrs
  cur.next = prev;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sent) {
      //assume false;
      return;
  }
  if (cur == null) {
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sent);
}

/*
# swl-4-addr-llb2.ss -tp om --pcp


 xform: ((AndList( "":self!=null ; "S":exists(M1:M=union(M1,{self}))
            ; "n":g!=self & s!=self) ) | (AndList( "S":M={}
            ; "n":g=self & s!=self) ))
  
translation below is wrong:
void lscan$node~node~node(  node cur,  node prev,  node sent) rec
static  :EBase exists (Expl)(Impl)[M1; b; a; M2](ex)EXISTS(b_36,
        a_37: cur::lx<a,b,M1>@M * prev::lx<b_36,a_37,M2>@M&
        AndList( "n":a!=cur & (((a=null & b=sent) | (a=sent & b=null))) & 
                 b=b_36 & a=a_37) &
        {FLOW,(22,23)=__norm})[]
          EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                  EAssume ref [cur;prev]
                    EXISTS(sent_38,flted_32_35,
                    c: prev'::lx<c,sent_38,flted_32_35>@M&
                    AndList( "":flted_32_35=union(M1,M2)
                     ; "n":c=null & cur'=sent & sent=sent_38) &
                    {FLOW,(22,23)=__norm})[]

Since we pre-declare:
  lx<"n":g,"n":s,"S":M> == ...

Should be:
           AndList( "M":flted_32_35=union(M1,M2)

*/
