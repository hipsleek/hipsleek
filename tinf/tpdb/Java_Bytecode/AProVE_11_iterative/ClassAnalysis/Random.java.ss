
global String[] Random_args;

global int Random_index = 0;
data Random
{

}
 int Random_random()
{
  String string = Random_args[Random_index];
  Random_index++;
  return String_length();
}



data ClassAnalysis
{
A field;
}
 void ClassAnalysis_main(String[] args)
{
  Random_args = args;
  ClassAnalysis t = new ClassAnalysis();
  t.field = new A();
  t.field = new B();
  ClassAnalysis_eval();
}

void ClassAnalysis_eval(ClassAnalysis _this)
{
