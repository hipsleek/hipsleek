

data SharingAnalysis
{
int val;

SharingAnalysis field;
}
 void SharingAnalysis_main(String[] args)
{
  Random_args = args;
  SharingAnalysis t1 = new SharingAnalysis();
  SharingAnalysis t2 = SharingAnalysis_appendNewList(1);
  SharingAnalysis t3 = SharingAnalysis_appendNewList(Random_random());
  t2.field = null;
  SharingAnalysis_copy(t1, t3);
}

void SharingAnalysis_copy(SharingAnalysis source, SharingAnalysis target)
{
  while (source != null) {
    SharingAnalysis newEle = new SharingAnalysis();
    newEle.val = source.val;
    target.field = newEle;
    source = source.field;
    target = target.field;
  }
}

SharingAnalysis SharingAnalysis_appendNewList(SharingAnalysis _this, int i)
{
  this_field = new SharingAnalysis();
  SharingAnalysis cur = this_field;
  while (i > 1) {
    i--;
    cur = cur.field = new SharingAnalysis();
  }
  return cur;
}


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

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;