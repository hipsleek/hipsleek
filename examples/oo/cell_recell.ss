Cell c1(Object start)
	static
		requires start::Object<>$
		ensures res::Cell<c>$ * c::Object<>$ & c=start;
{ 
	Cell tmp = new Cell(start);
	tmp.contents = start;
	return tmp;
}

/*********** CELL *****************/
class Cell extends Object {
	Object contents;
	
	void set(Object update)
		static
			requires this::Cell<c> * c::Object<> * update::Object<>
			ensures this::Cell<c1> * c1::Object<> & c1 = update;
		dynamic
			requires this::Cell<c>$ * c::Object<>$ * update::Object<>$
			ensures this::Cell<c1>$ * c1::Object<>$ & c1 = update;
	{
		this.contents = update;
		return;
	}
	
	Object get() 
		static
			requires this::Cell<c> * c::Object<>
			ensures this::Cell<c> * c::Object<> & res = c;
		dynamic
			requires this::Cell<c>$ * c::Object<>$
			ensures this::Cell<c>$ * c::Object<>$ & res = c;	{
		Object temp;
		temp = this.contents;
		return temp;
	}
}

Recell c2(Object start)
	static
		requires start::Object<>
		ensures res::Recell<u, c> * u::Object<> * c::Object<> & c=start;
	dynamic
		requires start::Object<>$
		ensures res::Recell<u, c>$ * u::Object<>$ * c::Object<>$ & c=start;
{
	Recell tmp = new Recell(start, tmp);
	tmp.contents = start;	// -- super(start);
	tmp.undo = null;
	return tmp;
}

/************* RECELL *****************/
class Recell extends Cell{
	Object undo;
	
	void set(Object update)
	static
		requires this::Recell<u, c> * u::Object<> * c::Object<> * update::Object<>
		ensures this::Recell<u1, c1> * u1::Object<> * c1::Object<> & u1=c & c1=update; 
	dynamic
		requires this::Recell<u, c>$ * u::Object<>$ * c::Object<>$ * update::Object<>$
		ensures this::Recell<u1, c1>$ * u1::Object<>$ * c1::Object<>$ & u1=c & c1=update; 

	{
		this.undo = this.contents;
		this.contents = update;
		return;
	}
}
