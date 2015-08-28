/*@
WFS<> ==
  self::char_star<0,q>*q::BADS<> 
  or self::char_star<v,q>*q::WFS<> & v!=0 
  inv true;

WFSeg<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;
*/

// s1 is now two strings one after another..
char *(cstrcat)(char *s1, const char *s2)
  /*@
    requires s1::WFS<> * s2::WFS<> 
    ensures s1::WFSeg<q2>*q2::char_star<0,res> *  s2::WFSeg<q>*q::char_star<0,qq>*qq::BADS<> 
    * res::WFSeg<q4>*q4::char_star<0,q5>*q5::BADS<>;
  */
  {
     while (*s1++!='\0') 
       /*@
          requires s1::WFS<> 
          ensures s1::WFSeg<q>*q::char_star<0,s1'>*s1'::BADS<>;
       */
       {
         //s1++;
       }
     char *t1 = s1;
     while ((*s1++ = *s2++) != '\0')
       /*@
          requires s1::char_star<_,q> * q::BADS<> * s2::WFS<>   
          ensures s2::WFSeg<qq>*qq::char_star<0,s2'>*s2'::BADS<> 
              * s1::WFSeg<q4>*q4::char_star<0,s1'>*s1'::BADS<>;
       */
       ;
     return t1;
  }

char* new_str()
  /*@
     requires emp
     ensures res::WFS<>;
  */
 {}

int main() 
  /*@
     requires true
     ensures res=0;
  */ 
{
  char *s1 = new_str();
  char *s2 = new_str();
  cstrcat(s1, s2);
  return 0;
}


/*
# was ex12f.c with full spec

=============================================================
Why this post condition cannot be derived?

Message: Post condition cannot be derived.
Procedure while_23_5$char_star~char_star FAIL.(2)
Exception Failure("Post condition cannot be derived.") Occurred!
Error(s) detected when checking procedure while_23_5$char_star~char_star

Message: Post condition cannot be derived.
Procedure while_23_5$char_star~char_star FAIL.(2)
Exception Failure("Post condition cannot be derived.") Occurred!
Error(s) detected when checking procedure while_23_5$char_star~char_star


--> while (*s++!='\0'){} is different from while(*s!='\0'){s++} --> How to solve?
*/

--> while (*s++!='\0'){} is different from while(*s!='\0'){s++} --> How to solve?
*/
