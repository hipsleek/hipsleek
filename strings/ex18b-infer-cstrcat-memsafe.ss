/*
 char *(cstrcat)(char *s1, const char *s2)
 {
     char *s = s1;
     while (*s != '\0')
         s++;
     while ((*s++ = *s2++) != '\0')
         ;               
     return s1;
 }

int main() {
  char *s1;
  char *s2;
  cstrcat(s1, s2);
  return 0;
}
*/

data str {
  int val;
  str next;
}

WFS<n:int,k:int,m:int> ==
  self::str<0,q>*q::BADS<m> & n=k
  or self::str<v,q>*q::WFS<n+1,k,m> & v>0 & n<k
  inv n<=k & m>=0;

WFSeg<n:int,p> ==
  self=p & n=0
  or self::str<v,q>*q::WFSeg<n-1,p> & v>0 
  inv n>=0;

BADS<m> ==
  self=null & m=0 or
  self::str<v,q>*q::BADS<m-1> & v>=0 
  inv m>=0;

str incStr(str x)
  requires x::str<_,q>@L & Term[]
  ensures  res=q ;
/*
  requires x::WFS<n,k,m> & Term[]
  case { 
    n!=k  -> ensures x::str<v,res> * res::WFS<n+1,k,m> & v>0;
    n=k  ->  ensures x::str<0,res> * res::BADS<m>;
  }
  requires x::BADS<m> & Term[] & m>0
  ensures x::str<v,res> * res::BADS<m-1> & v>=0;
*/

void assignStr(str x,int v)
  requires x::str<_,q> & Term[]
  ensures  x::str<v,q> ;

int getChar(str x)
  requires x::str<v,q>@L & Term[]
  ensures res=v;
 
/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..
*/
relation PPP(int a, int b, int c,int d, int e).

void while1(ref str s)
  infer [PPP]
  requires s::WFS<n,k,m> 
  ensures s::WFSeg<n1,s'>*s'::str<0,q>*q::BADS<mmmm> & PPP(n,k,m,mmmm,n1);
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
  }
}

/*
# ex18a.ss

# Parameter re-arrangment for fixcalc.
  Need to reverse it..

(==fixcalc.ml#1475==)
arrange_para_new@1
arrange_para_new inp1 :[( PPP(mmmm_1371,n1_1372,n,k,m),[ PPP(mmmm_1371,n1_1460,n_1446,k,m) & 0<=n1_1460 & 0<=m & n_1446<=k & 
 n=n_1446-1 & n1_1372=n1_1460+1 & 0<=mmmm_1371, n1_1372=0 & k=n & mmmm_1371=m & 0<=m])]
arrange_para_new inp2 :[n,k,m,s]
arrange_para_new@1 EXIT:[( PPP(n,k,m,mmmm_1371,n1_1372),[ 0<=n1_1460 & 0<=m & n_1446<=k & n=n_1446-1 & n1_1372=n1_1460+1 & 
 0<=mmmm_1371 & PPP(n_1446,k,m,mmmm_1371,n1_1460), n1_1372=0 & k=n & mmmm_1371=m & 0<=m])]


# Why did s::WFSEg<...> disappeared below?
  What happen to PPP(...)??

!!! **pi.ml#831:lst_assume (after norm and postprocess):[]
!!! **pi.ml#835:new_specs2:
[ EInfer [P]
   EBase 
     exists (Expl)[](Impl)[n; k; m](ex)[]s::WFS<n,k,m>@M&
     {FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         ref [s]
         (exists s_1373,flted_71_1374,q_1375,m1_1376,
         n1_1377: s'::str<flted_71_1374,q_1375>@M * q_1375::BADS<m1_1376>@M&
         flted_71_1374=0 & s_1373=s' & n<=k & 0<=m&{FLOW,(4,5)=__norm#E}[]]


(==fixpoint.ml#149==)
drop_rel_formula@28@27
drop_rel_formula inp1 : flted_71_1374=0 & PPP(mmmm_1376,n1_1377,n,k,m) & s_1373=s' & n<=k & 0<=m
drop_rel_formula@28 EXIT: flted_71_1374=0 & true & s_1373=s' & n<=k & 0<=m

(==fixpoint.ml#239==)
drop_rel_formula@29@27
drop_rel_formula inp1 : MayLoop[]
drop_rel_formula@29 EXIT: MayLoop[]

(==fixpoint.ml#239==)
drop_rel_formula@30@27
drop_rel_formula inp1 : true
drop_rel_formula@30 EXIT: true

(==pi.ml#833==)
simplify_relation@27
simplify_relation inp1 : EInfer [P]
   EBase 
     exists (Expl)[](Impl)[n; k; m](ex)[]s::WFS<n,k,m>@M&
     {FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         ref [s]
         (exists s_1373,flted_71_1374,q_1375,mmmm_1376,
         n1_1377: s::WFSeg<n1_1377,s_1373>@M * 
                  s'::str<flted_71_1374,q_1375>@M * q_1375::BADS<mmmm_1376>@M&
         flted_71_1374=0 & PPP(mmmm_1376,n1_1377,n,k,m) & s_1373=s' & n<=k & 
         0<=m&{FLOW,(4,5)=__norm#E}[]
simplify_relation inp2 :Some([( PPP(n,k,m,mmmm_1371,n1_1372), n1_1372>=0 & mmmm_1371>=0 & mmmm_1371=m & n1_1372+n=k, true)])
simplify_relation inp3 :lst_assume:[]
simplify_relation@27 EXIT:( EInfer [P]
   EBase 
     exists (Expl)[](Impl)[n; k; m](ex)[]s::WFS<n,k,m>@M&
     {FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         ref [s]
         (exists s_1373,flted_71_1374,q_1375,mmmm_1376,
         n1_1377: s::WFSeg<n1_1377,s_1373>@M * 
                  s'::str<flted_71_1374,q_1375>@M * q_1375::BADS<mmmm_1376>@M&
         flted_71_1374=0 & s_1373=s' & n<=k & 0<=m&{FLOW,(4,5)=__norm#E}[],[])

!!! **pi.ml#835:new_specs2:
[ EInfer [P]
   EBase 
     exists (Expl)[](Impl)[n; k; m](ex)[]s::WFS<n,k,m>@M&
     {FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         ref [s]
         (exists s_1373,flted_71_1374,q_1375,mmmm_1376,
         n1_1377: s::WFSeg<n1_1377,s_1373>@M * 
                  s'::str<flted_71_1374,q_1375>@M * q_1375::BADS<mmmm_1376>@M&
         flted_71_1374=0 & s_1373=s' & n<=k & 0<=m&{FLOW,(4,5)=__norm#E}[]]
Post Inference result:
while1$str
 EBase 
   exists (Expl)[](Impl)[n; k; m](ex)[]s::WFS<n,k,m>@M&MayLoop[]&
   {FLOW,(4,5)=__norm#E}[]
   EAssume 
     ref [s]
     (exists s_1373,flted_71_1374,q_1375,mmmm_1376,
     n1_1377: s::WFSeg<n1_1377,s_1373>@M * s'::str<flted_71_1374,q_1375>@M * 
              q_1375::BADS<mmmm_1376>@M&
     flted_71_1374=0 & s_1373=s' & n<=k & 0<=m&{FLOW,(4,5)=__norm#E}[]
Stop Omega... 352 invocations 
0 false contexts at: ()

 */
