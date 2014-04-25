data node {
  int val;
  node next;
}

sumll<s> == self=null & s=0
  or self::node<v,q>*q::sumll<s-v>
  inv true;

sumls<p,s> == self=p & s=0
  or self::node<v,q>*q::sumls<p,s-v> 
  inv true;
/*
lemma_unsafe "xx" self::sumll<s> <-> (exists a,b: self::sumls<p,a> * p::sumll<b> & s=a+b);

lemma_safe "yy" self::sumls<p,s> <- (exists a,v: self::sumls<q,a> * q::node<v,p> & s=a+v);
*/

lemma_safe "x4" self::sumll<s> <-> self::sumls<null,s>;

lemma_safe "x2" self::sumll<s> <-> self::sumls<self,0>*self::sumls<null,s>;


lemma_safe "yy" self::sumls<p,s> <- 
   (exists a,v: self::sumls<q,a> * q::node<v,p> & s=a+v);

/* 
# wand-2.ss --pcp

while loop translation error 

Whis is ys not captured as parameter of translated loop?

void f_r_910_while_64_2$int~node(  int sum_41,  node xs_40)
@ref sum_41, xs_40
 rec
static  :EBase exists (Expl)[](Impl)[ys; k](ex)[](exists xs_911,
        sum_912: ys::sumls<xs_911,sum_912>@L * xs_40::sumll<k>@L&
        xs_40=xs_911 & sum_41=sum_912&{FLOW,(24,25)=__norm})[]
          EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                  EAssume ref [sum_41;xs_40]
                    emp&sum_41'=k+sum_41 & xs_40'=null&
                    {FLOW,(24,25)=__norm}[]
                    
d
*/


int sumloop(node ys) 
  requires ys::sumll<s>@L
  ensures res = s;
{
  node xs=ys;
  int sum = 0;
  while (xs!=null)
    requires ys::sumls<xs,sum>@L * xs::sumll<k>@L 
    ensures  sum'=sum+k & xs'=null;  
  { 
     sum = sum + xs.val;
     xs = xs.next;
  }
  return sum;
}

