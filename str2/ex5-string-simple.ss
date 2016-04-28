void gen(ref string x)
  requires true
  ensures x'="abc";
{
  x = "abcd";
}
