

void loop()
 requires Loop
  ensures false;

bool non_det()
 requires true & Term[]
  ensures true;

void foo(int x)
 infer [@term]
 requires true
 ensures true;
{
  bool b = non_det();
  //assume !b;
  if (b) return;
  else loop();
}


void foo2(int x,bool non_b)
 infer [@term]
 requires true
 ensures true;
{
  bool b = non_b;
  if (b) return;
  else return; //loop();
}
