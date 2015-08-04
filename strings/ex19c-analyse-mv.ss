
data char_star {
  int val;
  char_star next;
}


pred_prim SA<y:char_star,rw:int> 
  inv 0<=rw<=2;

char_star plus_plus_char(char_star x)
  requires x::SA<y,rw>@L
  ensures  res::SA<y,rw> & res!=x;

void assign_char(char_star x,int v)
  requires x::SA<y,rw>
  ensures  x::SA<y,2> ;

int get_char(char_star x)
  requires x::SA<y,rw>@L
  ensures  x::SA<y,1> ;

lemma self::SA<y,r1>*self::SA<y,r2> -> self::SA<y,max(r1,r2)>.
 
/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..

  below is  tail-recursive function with 
  the same effect as loop

*/

void while1(ref char_star s)
  requires s::SA<y,rw>
  ensures  s::SA<y,max(1,rw)>;
{
  int x=get_char(s);
  if (x!=0) {
    s = plus_plus_char(s);
    while1(s);
  }
}


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

