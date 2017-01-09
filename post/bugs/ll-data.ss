data node {
  int val;
  node next;
}

ll<> == self=null
  or self::node<_,q> * q::ll<>;

int foo(node x)
  infer [@post_n]
  requires x::ll<>
  ensures x::ll<>;
{
  if (x == null)
    return 0;
  else
    return x.val;
}

/*

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN post_1223: ( res=0) -->  post_1223(res),
RELDEFN post_1223: ( true) -->  post_1223(res)]
*************************************
fixcalc: Parse error on line 1 rest of line:  -> [] -> []: (0=0 && self<=0) ||  exists (Anon_12,NODq: (self>0 && ll(NODq,)) && 1=1)

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1223(res), res=0, true, true)]
*************************************

!!! REL POST :  post_1223(res)
!!! POST:  res=0
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
foo$node
 requires x::ll<> & MayLoop[]
     ensures x::ll<> & res=0;

*/
