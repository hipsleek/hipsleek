
/*@
ll<n> == self=null & n=0
  or self::char_star<_,q>*q::ll<n-1>
inv n>=0.

lseg<p,n> == self=p   & n=0
  or self::char_star<_,q>*q::lseg<p,n-1>
inv n>=0.

cll<n> == self::char_star<_,q>*q::lseg<self,n-1>
inv n>=1;

lemma_safe self::lseg<p,n> <- self::lseg<q,m>*q::char_star<_,p> & n=m+1.

*/

int length(char* xs)
  /*@
     requires xs::cll<n>@L & Loop
     ensures false;
     requires xs::ll<n>@L & Term[n]
     ensures res=n;
  */
{
  if (xs == NULL) 
    return 0;
  xs++;
  return (1+length(xs));
}

void while1(char* xs)
  /*@
     requires xs::cll<n>
     ensures false;
     requires xs::ll<n>@L & Term[n]
     ensures true;
  */
{
  while (xs != NULL)
    /*@
       requires xs::cll<n>@L & Loop
       ensures false;
       requires xs::ll<n>@L & Term[n]
       ensures true;
    */
  {
    xs++;
  }
}
