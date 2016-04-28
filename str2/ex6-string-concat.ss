void c(ref string x, string y)
  requires true
  ensures x'="ab";
{
  string s = "a"^"b";
  x = s;
  int i = 1+2;
}
