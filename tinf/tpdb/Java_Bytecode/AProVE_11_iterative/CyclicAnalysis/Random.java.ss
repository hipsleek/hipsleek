
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



data CyclicAnalysis
{
CyclicAnalysis field;
}
 void CyclicAnalysis_main(String[] args)
{
  Random_args = args;
  CyclicAnalysis t = new CyclicAnalysis();
  t.field = new CyclicAnalysis();
  CyclicAnalysis_appendNewCyclicList(Random_random());
  CyclicAnalysis_appendNewList(Random_random());
  CyclicAnalysis_length();
}

int CyclicAnalysis_length(CyclicAnalysis _this)
{
  int length = 1;
  CyclicAnalysis cur = this_field;
  while (cur != null) {
    cur = cur.field;
    length++;
  }
  return length;
}

void CyclicAnalysis_appendNewCyclicList(CyclicAnalysis _this, int i)
{
