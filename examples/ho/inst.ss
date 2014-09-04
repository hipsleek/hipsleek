

data cell {
  int x;
}


int foo(cell c)
  requires c::cell<n>
  ensures  res=n+1;

int foo2(cell c)
  requires c::cell<n> & n>m
  ensures  res=n+1+m;


/*
# msg2.ss

static  :EBase exists (Expl)[](Impl)[a](ex)[]ch::MSG{ HVar P&{FLOW,(24,25)=__norm}[]}<a>@L&
        {FLOW,(24,25)=__norm}[]
          EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                  EAssume ref [c]
                    (exists P: HVar P&c'=a&{FLOW,(24,25)=__norm})[]

%P need to be made implicit on the pre-condition


*/
