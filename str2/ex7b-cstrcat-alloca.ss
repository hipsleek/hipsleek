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

// string head character
string sh(ref string s)
  case {
    slen(s) <= 0 -> ensures false;
    slen(s) > 0 -> ensures (exists s1, s2: s = s1^s2 & slen(s1) = 1 & res = s1);
  }

/*change this into tail-recursive
while ((*s++ = *s2++) != '\0')
         ;
*/

void loop2(ref string s, ref string s2)
  requires s = "" & slen(s2) = 0
  ensures false;
{
  string x = sh(s2);
  s = spp(s);
  s2 = spp(s2);
  /* if (sl(x) > 0) */
    loop2(s,s2);
}
