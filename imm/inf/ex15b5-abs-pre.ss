
data cell{
 int fst;
}

relation Q(ann v).

int foo2(cell c)
infer [Q]
  requires c::cell<_>@aaa & Q(aaa)
  ensures c::cell<_>@bbb;
{
  int x = 5;
  return x;
}

/*
# ex15b5.ss
Post Inference result:
foo2$cell
 EBase 
   exists (Expl)[](Impl)[aaa; Anon_11](ex)[]emp&aaa=@A & MayLoop[]&
   {FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists Anon_1197,bbb_1196: c::cell<Anon_1197>@bbb_1196&
     {FLOW,(4,5)=__norm#E}[]
*/
