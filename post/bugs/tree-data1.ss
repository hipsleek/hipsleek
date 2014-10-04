data node {
  int val;
  int height;
  node left;
  node right;
}

tree<> == self=null
  or self::node<_,h,l,r> * l::tree<> * r::tree<> & h>=0
  inv true;

int height(node x)
  infer [@post_n]
  requires x::tree<>
  ensures x::tree<>;
{
  if (x==null)
    return 0;
  else
    return x.height;
}

/*

*************************************
*******pure relation assumption ******
*************************************
[RELDEFN post_1232: ( res=0) -->  post_1232(res),
RELDEFN post_1232: ( 0<=res) -->  post_1232(res)]
*************************************
fixcalc: Parse error on line 1 rest of line:  -> [] -> []: (0=0 && self<=0) ||  exists (Anon_14,h,NODl,NODr: ((self>0 && tree(NODl,)) && tree(NODr,)) && 0<=h)

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1232(res), 0<=res, true, true)]
*************************************

!!! REL POST :  post_1232(res)
!!! POST:  0<=res
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
height$node
 requires x::tree<> & MayLoop[]
     ensures x::tree<> & 0<=res;

*/
