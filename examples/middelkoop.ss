

/*data str {
  String val;
}
str Str(String s)
	requires true
	ensures res::str<_>;
	{
  		return new str(s);
 	}
void concat(str ths, String s)
	requires ths::str<_>
	ensures ths::str<_>;
	{
  	// catenate s to ths.val	
 	}

data book {
   str title;
  // inv title!=null
}

bookI<s> == self::book<s>*s::str<_> inv true;
bookI2<s> == self::book<s> & s!=null inv s!=null;
//bookI<s> == self::book<s>*a::str<_> inv true;
// a is unreachable but VERIS did not detect
book Book()
	requires true
	ensures res::bookI<_>;
	{
                String i;
		str s=Str(i); //"unknown");
                return new book(s);
 	}
str getTitle(book ths)
	requires ths::bookI<s>
	ensures ths::bookI<s>;
	{ return ths.title;
	}
void setTitle(book ths,str n)
	requires ths::bookI<s>*n::str<_>
	ensures ths::bookI<n>;
	requires ths::bookI<s> & n=null
	ensures ths::bookI<s>;
	{ if (n!=null) ths.title=n;
	}*/


data Member {
	Book loaned;
	//inv loaned = null or loaned.loanedTo = this; 
}

data Book {
	Member loanedTo;
	//inv loanedTo = null or loanedTo.loaned = this;
}

MemberI<b> == self::Member<b> & b = null
	or self::Member<b> * b::Book<self>;

BookI<m> == self::Book<m> & m = null
	or self::Book<m> * m::Member<self>;

PairMB<b> == self::Member<b> * b::Book<self>;
PairBM<m> == self::Book<m> * m::Member<self>;


//----------------------------- lemmas ------------------------------------------
//MemberView<b> == self::Member<b>;
//BookView<m> == self::Book<m>;
//lemma "MB" self::MemberView<b> * b::BookView<self> <-> b::BookView<self> * self::MemberView<b>;

//lemma "MemberBook" self::MemberI<b> & b != null <-> b::Book<self> & self != null; 
void lemma_right(Member s)
	requires s::MemberI<b> & b!=null
	ensures b::BookI<s> & s!=null;
	

void lemma_left(Book s)
	requires s::BookI<m> & m!=null
	ensures m::MemberI<s> & s!=null;
	requires true
	ensures true;


//-----------------------------------------------------------------------------------
void loan(Member t, Book b) 
	requires t::MemberI<null> * b::BookI<null>
	ensures t::MemberI<b> & b != null;
	
	requires t::Member<null> * b::Book<null>
	ensures t::PairMB<b>;	
{
	t.loaned = b;
	loanTo(b, t);
	//assert b'::BookI<t> & t != null;
	// lemma step
	lemma_left(b);
	//dprint; 
}

void loanTo(Book t, Member m) 
	requires t::BookI<null> * m::Member<t>
	ensures t::BookI<m> & m != null;

	requires t::Book<null> * m::Member<t>
	ensures m::PairMB<t>;
{
	t.loanedTo = m; 
}

//------ subject - observer ----------------------------------------------------------

data Subject {
	int d;
	Observer co;
}

data Observer {
	Subject cs;
	int i;
}

ObserverIJ<cs, i> == self::Observer<cs, i> * cs::Subject<d, co> & i = d & co = self;
ObserverJ<cs, i, d> == self::Observer<cs, i> * cs::Subject<d, co> & co = self;

//lemma "IJ2J" self::ObserverIJ<cs, i> -> self::ObserverJ<cs, i, i>;


void setD(Subject s, int newD) 
	requires s::Subject<d, co> * co::Observer<s, d>
	ensures  co::ObserverIJ<s, newD>;
{
	//assert s'::Subject<_, _>;
	s.d = newD;	
	if(s.co != null) 
		update(s.co, newD);

}


void attach(Subject s, Observer o) 
	requires s::Subject<d, null> * o::Observer<s, _> 
	ensures o::ObserverIJ<s, d>;
{	
	s.co = o;
	//assert s'::Subject<_, _>;
	//assert o'::Observer<cs, i> * s'::Subject<_, _>;//* cs::Subject<_, _>;
	update(o, s.d);
}

int getVal(Observer o) 
	requires o::ObserverIJ<cs, i>
	ensures o::ObserverIJ<cs, i> & res = i;
{
	//assert o::Observer<_, _>;
	//dprint;
	return o.i;
}

void update(Observer o, int d) 
	requires o::ObserverJ<cs, i, d> 
	ensures o::ObserverIJ<cs, d>;
{
	o.i = d;
} 

