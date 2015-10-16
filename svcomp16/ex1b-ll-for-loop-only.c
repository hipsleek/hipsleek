
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

void for1(char* xs)
  /*@
     requires xs::cll<n>
     ensures false;
  */
{
  for (; xs != NULL; xs++)
    /*@
       requires xs::cll<n>
       ensures false;
    */
  ;
}

void for2(char* xs)
  /*@
     requires xs::ll<n>
     ensures true;
  */
{
  int length;
  for (length=0; xs != NULL; xs++, length++)
    /*@
       requires xs::ll<n>
       ensures xs'::ll<m>&m =0;
    */
  ;
}
