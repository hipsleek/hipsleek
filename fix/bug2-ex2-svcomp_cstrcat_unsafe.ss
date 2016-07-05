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

pred_prim STR<n:int,k:int> inv 0<=n<=k;
pred_prim WSTR<> inv true;

lemma self::STR<a,b> -> self::WSTR<>;

STR incStr(STR x)
  requires x::STR<n,k>@L & n<k & Term[]
  ensures res::STR<n+1,k>;
  requires x::STR<n,k>@L & n=k & Term[]
  ensures res::WSTR<>;
  requires x::WSTR<>@L & Term[]
  ensures res::WSTR<>;

void assignStr(STR x,int v)
  requires x::WSTR<>@L & Term[]
  ensures emp;

int getChar(STR x)
  requires x::STR<n,k>@L & Term[]
  case { 
    n=k -> ensures res=0;
    n!=k -> ensures true;
  }
  requires x::WSTR<>@L //& Term[] // MayLoop cause problem?
  ensures emp;
 
/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..
*/
void while1(ref STR s)
  requires s::STR<n,k> & Term[k-n]
  ensures s'::STR<_,_>; // need to conclude s'::WSTR<>
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
  }
}

/*
     while ((*s++ = *s2++) != '\0')
         ;               
*/
void while2(ref STR s1,ref STR s2)
  requires s1::WSTR<>@L * s2::STR<n,k>@L & Term[k-n]
  ensures emp; 
{
  int x=getChar(s2);
  assignStr(s1,x);
  if (x!=0) {
    s2 = incStr(s2);
    s1 = incStr(s1);
    while2(s1,s2);
  }

}

/*
# bug2.ss

# Is termination proving assumption too strong here?
# lemma search creates choice! should not be more problem ..

Termination checking result: 
(55)->(55) (ERR: invalid transition)  Term[100; k-n] ->  MayLoop[]


Checking procedure while2$STR~STR... 
Procedure while2$STR~STR SUCCESS.


Termination checking result: 
(70)->(70) (ERR: invalid transition)  Term[101; k-n] ->  MayLoop[]

*/
