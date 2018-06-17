hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

/*
./hip msess/OOPSLA/ex4-audio-cloud.ss --sess --ann-vp
*/

data media{}

data file{
  media vid;
  media aud;
}

data sess{ }

relation EFF(media m) == true.

pred effv<vid> == self::media<> & EFF(vid);
pred effa<aud> == self::media<> & EFF(aud);

pred_prim Session<S,H1,H2,c1,c2>;
/****************/
/* GLOBAL SPECS */
/****************/
pred MEDIA_FILE<vid,aud> == self::file<vid,aud> * vid::media<> * aud::media<> ;
pred EFF_MEDIA_FILE<fd>  == self::file<vid,aud> * vid::effv<fd.vid> * aud::effa<fd.aud> ;

pred_sess_prot FILTER_HELPER<S:role,H1:role,H2:role,c1:chan,c2:chan,vid,aud> ==
       (S->H1:c1(v#v::media<> & v=vid) * S->H2:c2(v#v::media<> & v=aud)) ;;
       (H1->S:c1(v#v::effv<vid>) * H2->S:c2(v#v::effa<aud>)) ;

pred_sess_prot FILTER<S:role,vid,aud> == exists S1,S2,c1,c2: FILTER_HELPER<S,S1,S2,c1,c2,vid,aud> ;

pred_sess_prot CLOUD<C:role,S:role,c:chan> == exists vid,aud,fd:
       C->S:c(v#fd::MEDIA_FILE<vid,aud> & fd=v) ;; FILTER<S,vid,aud> ;; S->C:c(v#v::EFF_MEDIA_FILE<fd>);
       // file<vid0,aud0> * vid0::effv<vid> * aud0::effa<aud>) ;


/******************/
/* implementation */
/******************/
//resources annotated with @L are released back to the caller's state
Channel init_H1(file fd, sess s)
   requires fd::MEDIA_FILE<vid,aud>@L * s::Session<S,H1,H2,c1,c2>@L
   ensures  res::Chan{@S FILTER_HELPER<S@peer,H1,H2,c1@chan,c2,vid,aud>}<>;

Channel init_H2(file fd, sess s)
   requires fd::MEDIA_FILE<vid,aud>@L * s::Session<S,H1,H2,c1,c2>@L
   ensures  res::Chan{@S FILTER_HELPER<S@peer,H1,H2,c1,c2@chan,vid,aud>}<>;

void release_H(Channel c)
     requires c::Chan{@S emp}<>
     ensures  true;


/*============ HELPER ============*/
file Server_helper(file fd)
     requires  //c::Chan{@S CLOUD<C,S@peer,c@chan>}<> *
              fd::MEDIA_FILE<vid,aud> *
              @full[fd,vid,aud,c]
     ensures  res::EFF_MEDIA_FILE<fd> ;
{
 sess s;
 assume s'::Session<S,H1,H2,c1,c2>;

 Channel c1 = init_H1(fd,s);
 Channel c2 = init_H2(fd,s);

 media video = fd.vid;
 media audio = fd.aud;

 dprint;

 par{c1',c2',video',audio'}
 {
  case {c1',video'} c1'::Chan{@S %R1}<> * video'::media<> ->
       dprint;
       send(c1,video)[media];
  ||
  case {c2',audio'} c2'::Chan{@S %R2}<> * audio'::media<> ->
       send(c2,audio)[media];
 }
 dprint; /* attempt to access/modify video/audio/fd.vid/fd.aud would fail */

 par{c1',c2',fd,video,audio}
 {
  case {c1',video} c1'::Chan{@S %R3}<> ->
       video = receive(c1)[media];
  ||
  case {c2',audio} c2'::Chan{@S %R4}<> ->
       audio = receive(c2)[media];
 }
 release_H(c1);
 release_H(c2);

 fd.vid = video;
 fd.aud = audio;

 return fd;
}

/*============ SERVER ============*/
void Server(Channel c)
     requires  c::Chan{@S CLOUD<C,S@peer,c@chan>}<> *
               @full[fd,c]
     ensures   c::Chan{@S emp}<>;
{
 file fd = receive(c)[file];
 fd = Server_helper(fd);
 send(c,fd)[file];
}


/*============ SERVER ============*/
void Client(Channel c, file fd)
     requires  c::Chan{@S CLOUD<C@peer,S,c@chan>}<> * fd::MEDIA_FILE<vid,aud>
     ensures   c::Chan{@S emp}<> * fd::EFF_MEDIA_FILE<fd>;
{
 send(c,fd)[file];
 fd = receive(c)[file];
}
