class r{}
int t()
requires true
ensures res::r<>;
{
	return new r();
}
