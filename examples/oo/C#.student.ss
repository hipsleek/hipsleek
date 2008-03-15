class String {}


EnrollmentInfo c1(String i, int g) 
	static
		requires true
		ensures res::EnrollmentInfo<i, g>;
	dynamic
		requires true
		ensures res::EnrollmentInfo<i, g>;
{
	EnrollmentInfo tmp = new EnrollmentInfo(i, g);
	tmp.institution = i;
	tmp.grade = g;
	return tmp;
}

class EnrollmentInfo{
	String institution;
	int grade;
}

Transcript c2(EnrollmentInfo ei) 
static
requires ei::EnrollmentInfo<i, g>
ensures res::Transcript<ei>;
{
	Transcript tmp = new Transcript(ei);
	return tmp;
}

class Transcript{
	EnrollmentInfo ei;
}

Person c3(String name) 
static
requires name::String<>
ensures res::Person<name>;
{
	Person tmp = new Person(name);
	tmp.name = name;
	return tmp;
}

class Person {
	String name;	
}

Student c4(String name, EnrollmentInfo ei) 
	static
		requires name::String<> * ei::EnrollmentInfo<i, g>	
		ensures res::Student<t, n> * t::Transcript<ei>;
	dynamic
		requires name::String<> * ei::EnrollmentInfo<i, g>	
		ensures res::Student<t, n> * t::Transcript<ei>;
{
	Transcript tmp1 = c2(ei);
	Student tmp = new Student(tmp1, name);
	/*super(name);*/
	tmp.t = tmp1;
	return tmp;
}

class Student extends Person {
	Transcript t;
	inv t != null;
}
