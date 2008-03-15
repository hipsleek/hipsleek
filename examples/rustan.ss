data master {
	int tm;
	int vers;
	// inv 0<=tm
  	// history inv vers<=vers';
  	// history inv vers=vers' -> tm <= tm';
}
  

data clock {
	master ms;
	int tm;
	int vers;
}

masterI<t, v> == self::master<t,v> & t>=0 inv t>=0;
 // this captures object invariant

masterH<t, v, t1, v1> == self::masterI<t1,v1> & t>=0 & v<=v1 & ( v!=v1 | t<=t1);
 // this captures history invariant of post-state

//clockI<ms, t, v> == self::clock<ms, t, v> & 0 <= t inv t>=0;
clockI<ms, t, v> == self::clock<ms, t, v> & ms != null & 0 <= t inv ms!=null & 0<=t;

MC2I<ms, t, v, mt, mv> == self::clock<ms, t, v> * ms::masterI<mt, mv> & t>=0 & v <= mv & (v != mv | t <= mt);

MC2Ie<t, v, mt, mv> == self::clock<ms, t, v> * ms::masterI<mt, mv> & t>=0 & v <= mv & (v != mv | t <= mt);

//MC2I<ms, t, v, mt, mv> == self::clockI<ms, t, v> * ms::masterI<mt, mv> & v <= mv & (v != mv | t <= mt);

MC2Ib<ms, t, v, mt, mv> == self::clock<ms, t, v> * ms::master<mt, mv> & mt>=0 & t>=0 & v <= mv & (v != mv | t <= mt);

//MC2Ib<ms, t, v, mt, mv> == ex tm . self::clock<ms, t, v> * ms::masterI<mt, mv> & tm>=0 & t>=0 & v <= mv & (v != mv | t <= mt);

MC2Ia<t, v, mt, mv> == self::clockI<ms, t, v> * ms::masterI<mt, mv> & v <= mv & (v != mv | t <= mt);

void foo(master m)
  requires m::master<n,a> & n>0 or m::master<n,n> & n<=0
  //ensures m::master<n,a> & n>0 or m::master<n,n> & n<=0;
  ensures m::master<n,a> & (n>0 | n<=0 & n=a);
{ }

master Master()
	requires true
	ensures res::masterI<0,0>;
	{
 		//master this1 = new master(0,0);
  		//this1.tm = 0; 
  		//this1.vers = 0;
  		return new master(0,0);
 	}


void Tick(master this1, int n)
 	requires this1::masterI<t,v> & n>=0
 	ensures this1::masterH<t,v,t+n,v>;
	{ 
		this1.tm = this1.tm+n; 
	}


void Reset(master this1)
 	requires this1::masterI<t,v> & n>=0
 	ensures this1::masterH<t,v,0,v+1>;
	{ 
		this1.vers = this1.vers+1; 
		this1.tm = 0;
	} 


//-----------------------------------------------------------

void Synch(clock this1) 
	requires this1::clock<ms, t, v> * ms::master<mt, mv>
	ensures this1::clock<ms, mt, mv> * ms::master<mt, mv>;
{
	this1.tm = this1.ms.tm;
	this1.vers = this1.ms.vers;

}

void Synch1(clock this1) 
	//requires this1::clock<ms, t, v> * ms::master<mt, mv>
	//ensures this1::clock<ms, mt, mv> * ms::master<mt, mv>;
	//requires this1::clockI<ms, t, v> * ms::masterI<mt, mv>
        // & v<=mv & (v != mv | t <= mt)
	//ensures this1::clockI<ms, mt, mv> * ms::masterI<mt,mv>
         //    & mv<=mv & (mv != mv | mt <= mt);
	//requires this1::MC2I< ms,t, v, mt, mv>
        //ensures this1::MC2I< ms,mt, mv, mt, mv>;
	requires this1::MC2Ie< t, v, mt, mv>
        ensures this1::MC2Ie< mt, mv, mt, mv>;
	requires this1::MC2Ib< ms,t, v, mt, mv>
	ensures this1::MC2Ib< ms,mt, mv, mt, mv>;
{
	this1.tm = this1.ms.tm;
	this1.vers = this1.ms.vers;

}

int GetTime(clock this1)
	requires this1::MC2Ib<ms, t, v, mt, mv>
	ensures this1::MC2Ib<ms, mt, mv, mt, mv> & v != mv & res = mt
		or this1::MC2Ib<ms, t, v, mt, mv> & v = mv & res = t;
        // why below cannot be used?
	//ensures this::MC2Ib<ms, t1, v1, mt, mv> & (v != mv & t1 = mt & v1 = mv | v = mv & t1 = t & v1 = v) & res = t1;
{
	//assert this1::MC2Ib<_,_,_,_,_>;	
	if (this1.vers != this1.ms.vers)
		Synch1(this1);
	//assert this1::MC2Ib<_,_,_,_,_>;
	return this1.tm;


}

//---------------------------------------------------------------------------
MC2I2<t, v, mt, mv> == self::clock<ms, t, v> * ms::master<mt, mv>;
MC2I3<ms, t, v, mt, mv> == self::clock<ms, t, v> * ms::master<mt, mv> & t >= 0 & mt >= 0 & v <= mv & (v != mv | t <= mt);
	//inv ms!=null & t >= 0 & mt >= 0;

void Synch2(clock this1) 
	requires this1::MC2I3<ms, t, v, mt, mv>
	ensures this1::MC2I3<ms, mt, mv, mt, mv>;
{
	this1.tm = this1.ms.tm;
	this1.vers = this1.ms.vers;
}


int GetTime2(clock this1)
	requires this1::MC2I3<ms, t, v, mt, mv>
	ensures this1::MC2I3<ms, mt, mv, mt, mv> & v != mv & res = mt
		or this1::MC2I3<ms, t, v, mt, mv> & v = mv & res = t;
	//ensures this::MC2I<ms, t1, v1, mt, mv> & (v != mv & t1 = mt & v1 = mv | v = mv & t1 = t & v1 = v) & res = t1;
{
	if (this1.vers != this1.ms.vers)
		Synch2(this1);
	//assert this1::MC2I3<_,_,_,_,_>;
	return this1.tm;


}
