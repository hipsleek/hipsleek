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

//lemma self::STR<a,b> -> self::WSTR<>;

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

// is it possible for strict alternatives..
int getChar(STR x)
  requires x::STR<n,k>@L & Term[]
  case { 
    n=k -> ensures res=0;
    n!=k -> ensures res!=0; // res!=0;
  }
  requires x::WSTR<>@L & Term[] // MayLoop cause problem?
  ensures emp;
 
/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..
*/
void loop1(ref STR s)
  requires s::STR<n,k>@L 
  case {
    n=k -> requires Term[] ensures true;
    n!=k -> requires Loop ensures false;
  }
  requires s::WSTR<>@L & MayLoop
  ensures true;
{
  int x=getChar(s);
  if (x!=0) {
    loop1(s);
  }
}

void loop2(ref STR s)
  requires s::STR<n,k>@L & Loop
  ensures false;
  requires s::WSTR<>@L & Loop
  ensures false;
{
  int x=getChar(s);
  loop2(s);
}


