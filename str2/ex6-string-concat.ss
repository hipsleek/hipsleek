void c(ref string x, string y)
  requires true
  ensures x' = "ab"^y;
{
  string s = "a"^"b"^y^"c";
  x = s;
  int i = 1+2;
}
