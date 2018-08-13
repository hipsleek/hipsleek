/***********************************/
/*  CLOUD - media filter service   */
/***********************************/


hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

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

pred_sess_prot CS<C:role,S:role,c:chan> == exists vid,aud,fd:
       C->S:c(v#fd::MEDIA_FILE<vid,aud> & fd=v) ;; FILTER<S,vid,aud> ;; S->C:c(v#v::EFF_MEDIA_FILE<fd>);

// CS <<STAR>> CLOUD is implicit despite the ;; between
// the first transmission and CLOUD, that is because
// the spec of c0 is released into the program state
// without any ordering constraint wrt CLOUD.
pred_sess_prot CLOUD<S:role,c:chan> == exists C,c0:
       C->S:c(v#v::Chan{@S CS<C,S@peer,v@chan>}<> & v=c0) ;;  CLOUD<S,c> ;

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
     requires fd::MEDIA_FILE<vid,aud> * @full[fd]
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

/*============   SEQ  ============*/
/*============ HELPER ============*/
file Server_helper_seq1(file fd)
     requires fd::MEDIA_FILE<vid,aud> * @full[fd]
     ensures  res::EFF_MEDIA_FILE<fd> ;
{
 sess s;
 assume s'::Session<S,H1,H2,c1,c2>;

 Channel c1 = init_H1(fd,s);
 Channel c2 = init_H2(fd,s);

 media video = fd.vid;
 media audio = fd.aud;

  send(c1,video)[media];
  send(c2,audio)[media];
  video = receive(c1)[media];
  audio = receive(c2)[media];

 release_H(c1);
 release_H(c2);

 fd.vid = video;
 fd.aud = audio;

 return fd;
}

file Server_helper_seq2(file fd)
     requires  fd::MEDIA_FILE<vid,aud> * @full[fd]
     ensures  res::EFF_MEDIA_FILE<fd> ;
{
 sess s;
 assume s'::Session<S,H1,H2,c1,c2>;

 Channel c1 = init_H1(fd,s);
 Channel c2 = init_H2(fd,s);

 media video = fd.vid;
 media audio = fd.aud;

  send(c2,audio)[media];
  send(c1,video)[media];
  video = receive(c1)[media];
  audio = receive(c2)[media];

 release_H(c1);
 release_H(c2);

 fd.vid = video;
 fd.aud = audio;

 return fd;
}


file Server_helper_seq3(file fd)
     requires fd::MEDIA_FILE<vid,aud> * @full[fd]
     ensures  res::EFF_MEDIA_FILE<fd> ;
{
 sess s;
 assume s'::Session<S,H1,H2,c1,c2>;

 Channel c1 = init_H1(fd,s);
 Channel c2 = init_H2(fd,s);

 media video = fd.vid;
 media audio = fd.aud;

  send(c2,audio)[media];
  send(c1,video)[media];
  audio = receive(c2)[media];
  video = receive(c1)[media];

 release_H(c1);
 release_H(c2);

 fd.vid = video;
 fd.aud = audio;

 return fd;
}

//below is OK to fail
file Server_helper_seq4_fail(file fd)
     requires fd::MEDIA_FILE<vid,aud> * @full[fd]
     ensures  res::EFF_MEDIA_FILE<fd> ;
{
 sess s;
 assume s'::Session<S,H1,H2,c1,c2>;

 Channel c1 = init_H1(fd,s);
 Channel c2 = init_H2(fd,s);

 media video = fd.vid;
 media audio = fd.aud;

  send(c1,video)[media];
  // FAIL CAUSE: the receives should be after all the sends
  video = receive(c1)[media];
  send(c2,audio)[media];
  audio = receive(c2)[media];

 release_H(c1);
 release_H(c2);

 fd.vid = video;
 fd.aud = audio;

 return fd;
}

//below is OK to fail
file Server_helper_seq_fail(file fd)
     requires fd::MEDIA_FILE<vid,aud> * @full[fd]
     ensures  res::EFF_MEDIA_FILE<fd> ;
{
 sess s;
 assume s'::Session<S,H1,H2,c1,c2>;

 Channel c1 = init_H1(fd,s);
 Channel c2 = init_H2(fd,s);

 media video = fd.vid;
 media audio = fd.aud;

  // FAIL CAUSE: receive on c2 should be after the send on c2
  audio = receive(c2)[media];
  send(c2,audio)[media];
  send(c1,video)[media];
  video = receive(c1)[media];

 release_H(c1);
 release_H(c2);

 fd.vid = video;
 fd.aud = audio;

 return fd;
}

/*============   PAR  ============*/
/*============ HELPER ============*/
file Server_helper_par1(file fd)
     requires fd::MEDIA_FILE<vid,aud> * @full[fd]
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

file Server_helper_par2(file fd)
     requires fd::MEDIA_FILE<vid,aud> * @full[fd]
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

 video = receive(c1)[media];
 audio = receive(c2)[media];

 release_H(c1);
 release_H(c2);

 fd.vid = video;
 fd.aud = audio;

 return fd;
}

file Server_helper_par3(file fd)
     requires fd::MEDIA_FILE<vid,aud> * @full[fd]
     ensures  res::EFF_MEDIA_FILE<fd> ;
{
 sess s;
 assume s'::Session<S,H1,H2,c1,c2>;

 Channel c1 = init_H1(fd,s);
 Channel c2 = init_H2(fd,s);

 media video = fd.vid;
 media audio = fd.aud;

 send(c1,video)[media];
 send(c2,audio)[media];

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
void Server_seq1(Channel c)
     requires  c::Chan{@S CS<C,S@peer,c@chan>}<>
     ensures   c::Chan{@S emp}<>;
{
 file fd = receive(c)[file];
 dprint;
 fd = Server_helper(fd);
 send(c,fd)[file];
}

/*=========== RECURSIVE ==========*/
/*============ SERVER ============*/
void Server_seq2(Channel c)
     requires  c::Chan{@S CLOUD<S@peer,c@chan>}<>
     ensures   false;
{
 Channel c0 = receive(c)[Channel];
 file fd = receive(c0)[file];
 dprint;
 fd = Server_helper(fd);
 send(c0,fd)[file];
 dprint;
 Server_seq2(c);
}

/*============ SERVER ============*/
void Server_par1(Channel c)
     requires  c::Chan{@S CLOUD<S@peer,c@chan>}<>
               * @full[c]
     ensures   false;
{
 Channel c0 = receive(c)[Channel];
 file fd = receive(c0)[file];
 dprint;
 par{c,c0',fd'}
 { case {c0',fd'} c0'::Chan{@S %R1}<> * fd'::MEDIA_FILE<_,_>->
       fd = Server_helper(fd);
       send(c0,fd)[file];
 ||
  case {c} c::Chan{@S %R2}<> ->
       Server_par1(c);
 }
}


/*============ CLIENT ============*/
void Client(Channel c, file fd)
     requires  c::Chan{@S CS<C@peer,S,c@chan>}<> * fd::MEDIA_FILE<vid,aud>
     ensures   c::Chan{@S emp}<> * fd::EFF_MEDIA_FILE<fd>;
{
 send(c,fd)[file];
 fd = receive(c)[file];
}
