// string length
int sl(string s)
  requires true
  ensures res = slen(s);


// string plus plus
string spp(ref string s)
  case {
    slen(s) <= 0 -> ensures false;
    slen(s) > 0 -> ensures (exists s1, s2: s = s1^s2 & slen(s1) = 1 & res = s2);
  }

/*change this into tail-recursive
while (*s != '\0')
         s++;
*/
void loop(ref string s)
  requires s = ""
  ensures false;
{
  /* if (sl(s) > 0) */
    loop(spp(s));
}

