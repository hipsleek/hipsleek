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

char *(cstrcat)(char *s1, const char *s2)
 /*@ 
     requires s1::char_star<_,_>*s2::char_star<_,q>
     ensures s1::char_star<_,q>;
 */
 {
     char *s = s1;
     s++;
     char x = *s2;
     *s = x;
     s++;
     s2++;
     return s1;
 }

/*int main() 
/*
     requires true
     ensures true;


{
  char *s1;
  char *s2;
  cstrcat(s1, s2);
  return 0;
}*/


