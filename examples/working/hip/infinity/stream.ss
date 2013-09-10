data stream{
	int fst;
	int snd;
	stream next;
}

inflist<n,p> == self = p & n = 0
	or self::stream<f,s,q> * q::inflist<n-1,p> & self != p
inv n >= 0;

fstlist<n,p> == self = p & n = 0
	or self::stream<f,s@A,q> * q::fstlist<n-1,p> & self != p
inv n >= 0;

sndlist<n,p> == self = p & n = 0
	or self::stream<f@A,s,q> * q::sndlist<n-1,p> & self != p
inv n >= 0;

void zip(stream x, stream y, stream z)
requires x::fstlist<\inf,null> * y::sndlist<\inf,null> * z::inflist<\inf,null>
ensures x::fstlist<\inf,null> * y::sndlist<\inf,null> * z::inflist<\inf,null>;
{
	int f = x.fst;
	int s = y.snd;
	z.fst = f;
	z.snd = s;
	zip(x.next,y.next,z.next);
}
