data node {
  node next;
}

lseg<p,n> == self=p & n=0
  or self::node<q>*q::lseg<p,n-1> & self!=p
  inv n>=0;


ll<p,n> == self=null & n=0
  or self::node<q>*q::ll<p,n-1> 
  inv n>=0;

/*
# case-1s.slk

--eci did not give case spec ...

 view ll<p:TVar[27],n:int>= 
  :EBase {1}->emp&self=null & n=0&{FLOW,(1,24)=__flow}[]
  || :EBase exists (Expl)[](Impl)[q](ex)[](exists p_13,
            flted_11_12: self::node<q>@M * q::ll<p_13,flted_11_12>@M&
            n=flted_11_12+1 & p=p_13&{FLOW,(1,24)=__flow})[]
*/
