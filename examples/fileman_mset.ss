/*
	File Manager:
	- tree of folders (left child/right sibling)
	- each folder holds a list of files and a list of folders

	Operations:
	- Create folder/file
	- Remove folder/file
	- Move/copy file/folder

	There is always a non-null root folder.

	Calling these operations: 
	simulating user inputs by using functions that ensures true/no size
*/

data str {
}

bool streq(str s1, str s2)
	requires true ensures true;

// path entry
data pentry {
	str ent;
	pentry next;
}

path<n> == self = null & n = 0
	or self::pentry<next = r> * r::path<n1> & n = n1 + 1
	inv n >= 0;

data file {
	str name;

	file next;
}

data folder {
	str name;
	
	file files;

	folder child;
	folder sib;
}

flist<n> == self = null & n = 0
	or self::file<name = fl, next = r> 
		* r::flist<n1> 
		& n = n1 + 1
	inv n >= 0;

// nf : total number of files
// nr : total number of folders
ftree<nf, nr> == self = null & nf = 0 & nr = 0
	or self::folder<name = fldr, files = fls, child = chd, sib = sb>
		* fls::flist<n1>
		* chd::ftree<nf1, nr1> * sb::ftree<nf2, nr2> 
		& nf = n1 + nf1 + nf2 & nr = 1 + nr1 + nr2
	inv nf >= 0 & nr >= 0;

fseg<p, nf, nr> == self = p & nf = 0 & nr = 0
	or self::folder<name = fldr, files = fls, child = chd, sib = sb>
		* fls::flist<n1>
		* chd::ftree<nf1, nr1> * sb::fseg<p, nf2, nr2>
		& nf = n1 + nf1 + nf2 & nr = 1 + nr1 + nr2
	inv nf >= 0 & nr >= 0;

lemma self::ftree<nf, nr> 
	<- self::fseg<x, nf1, nr1> * x::ftree<nf2, nr2> & nf = nf1 + nf2 & nr = nr1 + nr2;

lemma self::fseg<x, nf, nr> 
	<- self::fseg<r, nf1, nr1> * r::folder<files = fl, child = chd, sib = x>
		* fl::flist<n> * chd::ftree<nf2, nr2>
		& nf = nf1 + n + nf2 & nr = nr1 + nr2;

/*
	Search for a name in a folder list by following the sib link.
*/
folder search_name(str name, folder flist)
	requires flist::ftree<nf, nr>
	ensures flist::ftree<nf, nr> & res = null
		or flist::fseg<res, nf1, nr1> * res::ftree<nf2, nr2> 
			& nf = nf1 + nf2 & nr = nr1 + nr2 & res != null;
{
	if (flist != null) {
		if (streq(flist.name, name)) {
			return flist;
		}
		else {
			folder tmp = search_name(name, flist.sib);
			return tmp;
		}
	}
	else
		return null;
}

/*
	Make a folder with path pa in the folder tree rooted at fldr.
*/
bool mkdir(folder fldr, pentry pa)
	requires fldr::ftree<nf, nr> * pa::path<> & fldr != null
	ensures fldr::ftree<nf1, nr1> * pa::path<> & nf1 = nf & nr1 >= nr;
{
	bool ok = false;

	if (pa != null) {
		folder tmp = search_name(pa.ent, fldr.child);
		if (tmp != null) {
			ok = mkdir(tmp, pa.next);
			return ok;
		}
		else {
			// make a sub-folder as the left-most child
			tmp = new folder(pa.ent, null, null, fldr.child);
			fldr.child = tmp;
			mkdir(tmp, pa.next);
			ok = true;
			return ok;
		}
	}
	else {
		return ok;
	}
}

/*
	Remove a folder.

	Returns the removed tree; null if none removed.
*/
folder remove(folder fldr, pentry pa)
	requires fldr::ftree<nf, nr> * pa::path<> & fldr != null
	ensures fldr::ftree<nf1, nr1> * res::ftree<nf2, nr2> * pa::path<> 
		& nf = nf1 + nf2 & nr = nr1 + nr2;
{
	if (pa != null) {
		folder tmp = search_name(pa.ent, fldr.child);
		if (tmp != null) {
			if (pa.next != null) {
				tmp = remove(tmp, pa.next);
				return tmp;
			}
			else {
				fldr.child = delete_entry(fldr.child, tmp);
				return tmp;
			}
		}
		else {
			return null;
		}
	}
	else {
		return null;
	}
}

/*
	Return value: the updated l
*/
folder delete_entry(folder l, folder e)
	requires l::fseg<e, nf, nr> * e::ftree<nf1, nr1> & e != null
	ensures res::ftree<nf2, nr2> * e::ftree<nf3, nr3>
		& nf + nf1 = nf2 + nf3 & nr + nr1 = nr2 + nr3;
{
	if (l == null) {
		return l;
	}
	if (l == e) {
		folder tmp = l.sib;
		l.sib = null;
		return tmp;
	}

	if (l.sib == e) {
		l.sib = e.sib;
		e.sib = null;
		return l;
	}
	else {
		folder tmp = delete_entry(l.sib, e);
		l.sib = tmp;
		return l;
	}
}

/*
/*
	Find folder.
*/
folder find_folder(folder fldr, pentry pa)
	requires fldr::ftree<nf, nr> * pa::path<> & fldr != null
	ensures <needs to talk about tree with hole>
{
}
*/

/*
	Dup file.
*/
file dup_file(file f)
	requires f::flist<n>
	ensures res::flist<n> * f::flist<n>;
{
	if (f != null) {
		file tmp = dup_file(f.next);
		tmp = new file(f.name, tmp);
		return tmp;
	}
	else
		return null;
}

/*
	Duplicate folder.
*/
folder dup_folder(folder fldr)
	requires fldr::ftree<nf, nr>
	ensures fldr::ftree<nf, nr> * res::ftree<nf, nr>;
{
	if (fldr != null) {
		file new_files = dup_file(fldr.files);
		folder new_cld = dup_folder(fldr.child);
		folder new_sib = dup_folder(fldr.sib);
		folder new_fldr = new folder(fldr.name, new_files, 
						new_cld, new_sib);
		return new_fldr;
	}
	else
		return null;
}

/*
	Duplicate the named subfolder.
	Return null if the subfolder is not found.
*/
folder dup_path(folder fldr, pentry pa)
	requires fldr::ftree<nf, nr> * pa::path<n1> & fldr != null
	ensures fldr::ftree<nf, nr> * pa::path<n1> * res::ftree<nf1, nr1>
		& nf1 <= nf & nr1 <= nr;
{
	if (pa != null) {
		folder tmp = search_name(pa.ent, fldr.child);
		if (tmp != null) {
			if (pa.next != null) {
				tmp = dup_path(tmp, pa.next);
				return tmp;
			}
			else {
				tmp = dup_folder(tmp);
				return tmp;
			}
		}
		else {
			return null;
		}
	}
	else {
		return null;
	}
}

void append_child(folder fldr, folder new_f)
	requires fldr::ftree<nf1, nr1> * new_f::ftree<nf2, nr2>
		& fldr != null
	ensures fldr::ftree<nf3, nr3> & nf3 = nf1 + nf2 & nr3 = nr1 + nr2;
{
	if (fldr.child == null) {
		fldr.child = new_f;
		return;
	}
	else {
		append_sib(fldr.child, new_f);
		return;
	}
}

void append_sib(folder fldr, folder new_f)
	requires fldr::ftree<nf1, nr1> * new_f::ftree<nf2, nr2>
		& fldr != null
	ensures fldr::ftree<nf3, nr3> & nf3 = nf1 + nf2 & nr3 = nr1 + nr2;
{
	if (fldr.sib == null) {
		fldr.sib = new_f;
		return;
	}
	else {
		append_sib(fldr.sib, new_f);
		return;
	}
}

bool insert_path(folder fldr, folder new_f, pentry pa)
	requires fldr::ftree<nf, nr> * new_f::ftree<nf1, nr1> * pa::path<n> 
		& fldr != null & new_f != null
	ensures fldr::ftree<nf2, nr2> * pa::path<n>
		& res & nf2 = nf + nf1 & nr2 = nr + nr1
		or fldr::ftree<nf, nr> * new_f::ftree<nf1, nr1> * pa::path<n>
		& !res;
//	ensures fldr::ftree<nf2, nr2> * pa::path<n>;
{
	if (pa != null) {
		folder tmp = search_name(pa.ent, fldr.child);
		if (tmp != null) {
			if (pa.next != null) {
				bool ok = insert_path(tmp, new_f, pa.next);
				return ok;
			}
			else {
				append_child(tmp, new_f);
				return true;
			}
		}
		else {
			return false;
		}	
	}
	else {
		return false;
	}
}

/*
	Copy folder: copy a named folder to another name
	in the same file system. If "t" is the name of
	an existing folder, return false. Otherwise do
	the copy.
*/
bool copy_folder(folder fldr, pentry fr, pentry pa)
	requires fldr::ftree<nf, nr> * fr::path<n1> * pa::path<n2> 
		& fldr != null
	ensures fldr::ftree<nf1, nr1> * fr::path<n1> * pa::path<n2> 
		& nf1 >= nf & nr1 >= nr;
{
	folder tmp = dup_path(fldr, fr);
	if (tmp != null) {
		bool ok = insert_path(fldr, tmp, pa);
		return ok;
	}
	else {
		return false;
	}
}

/*******************************************
  Primitives
********************************************/

