data user{
  char* name;
  char* pass;
}



int login(ref user u, char* p)
  requires u::user<n,p>
  ensures  u'::user<n,p@A>;
{
  if(check_pass(p, u) != 0)
    return 1;
  else return 0;
}

int strcmp(char* s1, char* s2)
  requires true
  ensures true;
{
  return 1;
}

int check_pass(char* pass, ref user u)
  requires u::user<n,p>
  ensures  u'::user<n,p@A>;
{
  return strcmp(pass,u.pass);
}
