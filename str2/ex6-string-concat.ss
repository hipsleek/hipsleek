void c(ref string x, string y)
  case {
	y = "" -> ensures x' = "ab"^"c";
	y != "" -> ensures x' = "ab"^y^"c";
	}	
{
  string z = "abc";
  string s = "a"^"b"^y^"d";
  x = z;
  int i = 1+2;
}
